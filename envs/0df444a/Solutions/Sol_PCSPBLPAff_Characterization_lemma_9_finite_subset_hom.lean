-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_9_finite_subset_hom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:11.469333+00:00
-- url     : https://prove2.me/submissions/3aaed035-f1fa-46ea-9266-62a6d40c2b2d

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

open PCSPBLPAff.Characterization
open PCSPBLPAff.Symmetric

private lemma pos_of_blpAffObj {L : ℕ} (x : BLPAffObj (Fin L)) : 0 < L := by
  by_contra h
  have h0 : L = 0 := by omega
  subst h0
  have hsum := x.2.2.1
  simp at hsum

private def IsRepMap (u ℓ v Lstar L : ℕ) (x : BLPAffObj (Fin L)) (σ : Fin Lstar → Fin L) : Prop :=
  ∀ i : Fin L, (((Finset.univ.filter (fun l => σ l = i)).card : ℕ) : ℚ) =
    (u : ℚ) * ℓ * x.1.1 i + (v : ℚ) * (x.1.2 i : ℚ)

private def HasRepMap (u ℓ v Lstar L : ℕ) (x : BLPAffObj (Fin L)) : Prop :=
  ∃ σ : Fin Lstar → Fin L, IsRepMap u ℓ v Lstar L x σ

open Classical in
private noncomputable def chooseRepMap (u ℓ v Lstar L : ℕ) (x : BLPAffObj (Fin L)) :
    Fin Lstar → Fin L :=
  if h : HasRepMap u ℓ v Lstar L x then
    Classical.choose h
  else
    fun _ => ⟨0, pos_of_blpAffObj x⟩

open Classical in
private lemma chooseRepMap_spec {u ℓ v Lstar L : ℕ} {x : BLPAffObj (Fin L)}
    (h : HasRepMap u ℓ v Lstar L x) :
    IsRepMap u ℓ v Lstar L x (chooseRepMap u ℓ v Lstar L x) := by
  unfold chooseRepMap
  rw [dif_pos h]
  exact Classical.choose_spec h

private noncomputable def xiMap {A B : Type} (u ℓ v Lstar : ℕ) (f : (Fin Lstar → A) → B)
    (L : ℕ) (x : BLPAffObj (Fin L)) : (Fin L → A) → B :=
  polMinor (chooseRepMap u ℓ v Lstar L x) f

private lemma polMinor_eq_of_card_eq {A B : Type} {Lstar L : ℕ}
    (f : (Fin Lstar → A) → B) (hsym : IsSymmetric f)
    (σ₁ σ₂ : Fin Lstar → Fin L)
    (hfib : ∀ i : Fin L,
      (Finset.univ.filter (fun l => σ₁ l = i)).card =
      (Finset.univ.filter (fun l => σ₂ l = i)).card) :
    polMinor σ₁ f = polMinor σ₂ f := by
  have hcard : ∀ i : Fin L,
      Fintype.card {l : Fin Lstar // σ₁ l = i} = Fintype.card {l : Fin Lstar // σ₂ l = i} := by
    intro i
    rw [Fintype.card_subtype, Fintype.card_subtype, hfib i]
  let e : ∀ i : Fin L, {l : Fin Lstar // σ₁ l = i} ≃ {l : Fin Lstar // σ₂ l = i} :=
    fun i => Fintype.equivOfCardEq (hcard i)
  let ρ : Equiv.Perm (Fin Lstar) :=
    ((Equiv.sigmaFiberEquiv σ₁).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv σ₂)
  have hρ : ∀ l : Fin Lstar, σ₂ (ρ l) = σ₁ l := fun l => (e (σ₁ l) ⟨l, rfl⟩).2
  funext a
  unfold polMinor
  have hcomp : a ∘ σ₁ = (a ∘ σ₂) ∘ ρ := by
    funext l
    simp only [Function.comp_apply, hρ l]
  rw [hcomp, hsym ρ (a ∘ σ₂)]

private lemma isRepMap_comp (u ℓ v Lstar L L' : ℕ) (x : BLPAffObj (Fin L))
    (σ : Fin Lstar → Fin L) (hσ : IsRepMap u ℓ v Lstar L x σ)
    (π : Fin L → Fin L') (h : IsBLPAffObj (minorQ π x.1.1) (minorZ π x.1.2)) :
    IsRepMap u ℓ v Lstar L' ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩ (π ∘ σ) := by
  rcases x with ⟨⟨w, r⟩, hx⟩
  intro j
  have hbi : Finset.univ.filter (fun l : Fin Lstar => (π ∘ σ) l = j) =
      (Finset.univ.filter (fun i : Fin L => π i = j)).biUnion
        (fun i => Finset.univ.filter (fun l : Fin Lstar => σ l = i)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Function.comp_apply]
    exact ⟨fun h => ⟨σ l, h, rfl⟩, fun ⟨i, hi, hli⟩ => by rw [hli, hi]⟩
  have hdisj : (↑(Finset.univ.filter (fun i : Fin L => π i = j)) : Set (Fin L)).PairwiseDisjoint
      (fun i => Finset.univ.filter (fun l : Fin Lstar => σ l = i)) := by
    intro i₁ _ i₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro l hl₁ hl₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl₁ hl₂
    exact hne (hl₁.symm.trans hl₂)
  change (((Finset.univ.filter (fun l : Fin Lstar => (π ∘ σ) l = j)).card : ℕ) : ℚ) =
    (u : ℚ) * ℓ * minorQ π w j + (v : ℚ) * (minorZ π r j : ℚ)
  rw [hbi, Finset.card_biUnion hdisj, Nat.cast_sum]
  have hsum_eq : ∑ i ∈ Finset.univ.filter (fun i : Fin L => π i = j),
      (((Finset.univ.filter (fun l : Fin Lstar => σ l = i)).card : ℕ) : ℚ) =
    ∑ i ∈ Finset.univ.filter (fun i : Fin L => π i = j),
      ((u : ℚ) * ℓ * w i + (v : ℚ) * (r i : ℚ)) :=
    Finset.sum_congr rfl (fun i _ => hσ i)
  rw [hsum_eq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [minorQ, minorZ, Int.cast_sum]

private lemma exists_sigma_of_sum_eq (Lstar L : ℕ) (W : Fin L → ℕ) (hW : ∑ i : Fin L, W i = Lstar) :
    ∃ σ : Fin Lstar → Fin L,
      ∀ i : Fin L, (Finset.univ.filter (fun l => σ l = i)).card = W i := by
  have hcard_sigma : Fintype.card (Fin Lstar) = Fintype.card (Σ i : Fin L, Fin (W i)) := by
    rw [Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hW.symm
  let e : Fin Lstar ≃ Σ i : Fin L, Fin (W i) := Fintype.equivOfCardEq hcard_sigma
  refine ⟨fun l => (e l).1, fun i => ?_⟩
  have hmap : (Finset.univ.filter (fun l : Fin Lstar => (e l).1 = i)).map e.toEmbedding =
      (({i} : Finset (Fin L)).sigma (fun j => (Finset.univ : Finset (Fin (W j))))) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply, Finset.mem_sigma, Finset.mem_singleton, and_true]
    exact ⟨fun ⟨l, hl, hlp⟩ => by rw [← hlp, hl], fun hp => ⟨e.symm p, by simp [hp], by simp⟩⟩
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ,
    Fintype.card_fin] at hcard
  exact hcard

private lemma hasRepMap_of_mem_M (ℓ M Lstar u v : ℕ) (hℓ : 0 < ℓ) (hLstar : M * ℓ ^ 2 ≤ Lstar)
    (huv : Lstar = u * ℓ + v) (hv : v < ℓ) (L : ℕ) (x : BLPAffObj (Fin L))
    (hz : ∀ i, ∃ z : ℤ, (ℓ : ℚ) * x.1.1 i = z) (hr : ∑ i, |x.1.2 i| ≤ (M : ℤ)) :
    HasRepMap u ℓ v Lstar L x := by
  rcases x with ⟨⟨w, r⟩, hx⟩
  change ∀ i, ∃ z : ℤ, (ℓ : ℚ) * w i = z at hz
  change ∑ i, |r i| ≤ (M : ℤ) at hr
  choose z hz_eq using hz
  let W_int : Fin L → ℤ := fun i => (u : ℤ) * z i + (v : ℤ) * r i
  have hM_mul : v * M ≤ u := by
    have h1 : M * ℓ * ℓ ≤ u * ℓ + v := by
      calc M * ℓ * ℓ = M * ℓ ^ 2 := by ring
        _ ≤ Lstar := hLstar
        _ = u * ℓ + v := huv
    have h2 : u * ℓ + v < (u + 1) * ℓ := by
      calc u * ℓ + v < u * ℓ + ℓ := by omega
        _ = (u + 1) * ℓ := by ring
    have h3 : M * ℓ * ℓ < (u + 1) * ℓ := lt_of_le_of_lt h1 h2
    have h4 : M * ℓ < u + 1 := Nat.lt_of_mul_lt_mul_right h3
    have h5 : M * ℓ ≤ u := by omega
    have h6 : v * M ≤ M * ℓ := by
      calc v * M ≤ ℓ * M := Nat.mul_le_mul_right M (le_of_lt hv)
        _ = M * ℓ := Nat.mul_comm ℓ M
    exact le_trans h6 h5
  have hW_nonneg : ∀ i : Fin L, 0 ≤ W_int i := by
    intro i
    have hw_nonneg : 0 ≤ w i := hx.1 i
    rcases eq_or_lt_of_le hw_nonneg with hw0 | hw_pos
    · have hz0_q : (z i : ℚ) = 0 := by
        rw [← hz_eq i, ← hw0, mul_zero]
      have hz0 : z i = 0 := Int.cast_injective hz0_q
      have hr0 : r i = 0 := hx.2.2.2 i hw0.symm
      dsimp [W_int]
      rw [hz0, hr0]
      omega
    · have hℓ_pos_q : (0 : ℚ) < (ℓ : ℚ) := Nat.cast_pos.mpr hℓ
      have hz_pos_q : (0 : ℚ) < (z i : ℚ) := by
        rw [← hz_eq i]
        exact mul_pos hℓ_pos_q hw_pos
      have hz_pos : 0 < z i := Int.cast_lt.mp hz_pos_q
      have habs_le : |r i| ≤ (M : ℤ) := by
        have hle_sum : |r i| ≤ ∑ j : Fin L, |r j| :=
          Finset.single_le_sum (fun j _ => abs_nonneg (r j)) (Finset.mem_univ i)
        exact le_trans hle_sum hr
      have hri_ge : -(M : ℤ) ≤ r i := by
        have hneg : -|r i| ≤ r i := neg_abs_le (r i)
        linarith
      have hM_mul_z : (v : ℤ) * (M : ℤ) ≤ (u : ℤ) := by exact_mod_cast hM_mul
      have hu_le : (u : ℤ) ≤ (u : ℤ) * z i := by
        have hz1 : 1 ≤ z i := by omega
        nlinarith
      have hv_ge : -((v : ℤ) * (M : ℤ)) ≤ (v : ℤ) * r i := by
        nlinarith
      dsimp [W_int]
      linarith
  let W : Fin L → ℕ := fun i => (W_int i).toNat
  have hW_eq_q : ∀ i : Fin L, ((W i : ℕ) : ℚ) = (u : ℚ) * ℓ * w i + (v : ℚ) * (r i : ℚ) := by
    intro i
    have htoNat : ((W i : ℕ) : ℤ) = W_int i := Int.toNat_of_nonneg (hW_nonneg i)
    have hq : (((W i : ℕ) : ℤ) : ℚ) = (W_int i : ℚ) := congrArg Int.cast htoNat
    simp only [Int.cast_natCast] at hq
    rw [hq]
    dsimp [W_int]
    push_cast
    rw [← hz_eq i]
    ring
  have hW_sum : ∑ i : Fin L, W i = Lstar := by
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_sum]
    simp only [hW_eq_q]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Int.cast_sum]
    rw [hx.2.1, hx.2.2.1, huv]
    push_cast
    ring
  obtain ⟨σ, hσ⟩ := exists_sigma_of_sum_eq Lstar L W hW_sum
  refine ⟨σ, fun i => ?_⟩
  change (((Finset.univ.filter (fun l => σ l = i)).card : ℕ) : ℚ) =
    (u : ℚ) * ℓ * w i + (v : ℚ) * (r i : ℚ)
  rw [hσ i, hW_eq_q i]

theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (ℓ M Lstar u v : ℕ) (hℓ : 0 < ℓ) (hLstar : M * ℓ ^ 2 ≤ Lstar)
    (huv : Lstar = u * ℓ + v) (hv : v < ℓ)
    (f : (Fin Lstar → A) → B) (_hf : PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f) (hsym : PCSPBLPAff.Symmetric.IsSymmetric f) :
    ∃ ξ : (L : ℕ) → BLPAffObj (Fin L) → (Fin L → A) → B,
      ∀ (L : ℕ) (x : BLPAffObj (Fin L)),
        (∀ i, ∃ z : ℤ, (ℓ : ℚ) * x.1.1 i = z) → ∑ i, |x.1.2 i| ≤ (M : ℤ) →
          (∃ σ : Fin Lstar → Fin L,
              (∀ i, (((Finset.univ.filter (fun l => σ l = i)).card : ℕ) : ℚ) =
                (u : ℚ) * ℓ * x.1.1 i + (v : ℚ) * (x.1.2 i : ℚ)) ∧
              ξ L x = polMinor σ f) ∧
          ∀ (L' : ℕ) (π : Fin L → Fin L') (h : IsBLPAffObj (minorQ π x.1.1) (minorZ π x.1.2)),
            ξ L' ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩ = polMinor π (ξ L x) := by
  refine ⟨xiMap u ℓ v Lstar f, fun L x hz hr => ?_⟩
  have hrep : HasRepMap u ℓ v Lstar L x :=
    hasRepMap_of_mem_M ℓ M Lstar u v hℓ hLstar huv hv L x hz hr
  have hchoose : IsRepMap u ℓ v Lstar L x (chooseRepMap u ℓ v Lstar L x) :=
    chooseRepMap_spec hrep
  refine ⟨⟨chooseRepMap u ℓ v Lstar L x, hchoose, rfl⟩, fun L' π h => ?_⟩
  let x' : BLPAffObj (Fin L') := ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩
  have hcomp_rep : IsRepMap u ℓ v Lstar L' x' (π ∘ chooseRepMap u ℓ v Lstar L x) :=
    isRepMap_comp u ℓ v Lstar L L' x (chooseRepMap u ℓ v Lstar L x) hchoose π h
  have hrep' : HasRepMap u ℓ v Lstar L' x' := ⟨π ∘ chooseRepMap u ℓ v Lstar L x, hcomp_rep⟩
  have hchoose' : IsRepMap u ℓ v Lstar L' x' (chooseRepMap u ℓ v Lstar L' x') :=
    chooseRepMap_spec hrep'
  have hfib : ∀ j : Fin L',
      (Finset.univ.filter (fun l => chooseRepMap u ℓ v Lstar L' x' l = j)).card =
      (Finset.univ.filter (fun l => (π ∘ chooseRepMap u ℓ v Lstar L x) l = j)).card := by
    intro j
    apply Nat.cast_injective (R := ℚ)
    rw [hchoose' j, hcomp_rep j]
  unfold xiMap
  rw [polMinor_eq_of_card_eq f hsym (chooseRepMap u ℓ v Lstar L' x')
    (π ∘ chooseRepMap u ℓ v Lstar L x) hfib]
  rfl
