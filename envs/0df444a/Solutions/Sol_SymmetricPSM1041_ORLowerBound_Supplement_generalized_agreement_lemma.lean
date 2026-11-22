-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.Supplement.generalized_agreement_lemma
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T02:29:39.177569+00:00
-- url     : https://prove2.me/submissions/7e03703a-95b1-487e-858a-9044906e5671

import Mathlib

open Finset Classical
open scoped Real

namespace PlotkinProbe

-- (Plotkin's bound and the code step are copied below.)

/-- Plotkin's bound for `q`-ary codes of length `#ι`. -/
lemma plotkin_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {q M d : ℕ}
    (hq : 1 ≤ q) (C : Finset (ι → Fin q)) (hM1 : 1 ≤ M) (hM : C.card = M)
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ (Finset.univ.filter (fun j => x j ≠ y j)).card)
    (hden : 0 < (q : ℝ) * d - ((q : ℝ) - 1) * (Fintype.card ι)) :
    (M : ℝ) ≤ (q : ℝ) * d / ((q : ℝ) * d - ((q : ℝ) - 1) * (Fintype.card ι)) := by
  classical
  let m : ι → Fin q → ℝ := fun j σ => ((C.filter (fun x => x j = σ)).card : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : ∀ j : ι, ∑ σ, m j σ = (M : ℝ) := by
    intro j
    have hfib := Finset.sum_fiberwise_of_maps_to (s := C) (t := Finset.univ) (g := fun x => x j)
      (fun i _ => Finset.mem_univ _) (fun _ => (1 : ℝ))
    have hL : ∀ σ, ∑ x ∈ C.filter (fun x => x j = σ), (1 : ℝ) = m j σ := by
      intro σ
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hR : ∑ x ∈ C, (1 : ℝ) = (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hM]
    simp only [hL, hR] at hfib
    exact hfib
  have hcs : ∀ j : ι, (M : ℝ) ^ 2 / (q : ℝ) ≤ ∑ σ, (m j σ) ^ 2 := by
    intro j
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun σ => m j σ)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [div_le_iff₀ hqpos, ← hsum j]
    nlinarith [h]
  have hdist : ∀ x y : ι → Fin q,
      ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) =
        ∑ j : ι, (if x j ≠ y j then (1 : ℝ) else 0) := by
    intro x y
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    simp
  have hlow : (M : ℝ) * ((M : ℝ) - 1) * d ≤
      ∑ x ∈ C, ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) := by
    have hper : ∀ x ∈ C, ((M : ℝ) - 1) * d ≤
        ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) := by
      intro x hx
      have h1 : ∑ y ∈ C, (if y = x then (0 : ℝ) else (d : ℝ)) ≤
          ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hyx : y = x
        · subst hyx
          simp
        · simp only [hyx, if_false]
          exact_mod_cast hd x hx y hy (Ne.symm hyx)
      have h2 : ∑ y ∈ C, (if y = x then (0 : ℝ) else (d : ℝ)) = ((M : ℝ) - 1) * d := by
        have h2a : ∀ y, (if y = x then (0 : ℝ) else (d : ℝ)) = d - (if y = x then (d : ℝ) else 0) := by
          intro y
          by_cases h : y = x <;> simp [h]
        simp only [h2a, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.sum_ite_eq' C x (fun _ => (d : ℝ)), if_pos hx, hM]
        ring
      linarith
    calc (M : ℝ) * ((M : ℝ) - 1) * d = ∑ _x ∈ C, ((M : ℝ) - 1) * d := by
          rw [Finset.sum_const, hM, nsmul_eq_mul]
          ring
      _ ≤ ∑ x ∈ C, ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) :=
          Finset.sum_le_sum hper
  have hupper : ∑ x ∈ C, ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ) ≤
      (Fintype.card ι : ℝ) * ((M : ℝ) ^ 2 - (M : ℝ) ^ 2 / (q : ℝ)) := by
    have hstep1 : ∑ x ∈ C, ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ)
        = ∑ j : ι, ∑ x ∈ C, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0) := by
      calc ∑ x ∈ C, ∑ y ∈ C, ((Finset.univ.filter (fun j => x j ≠ y j)).card : ℝ)
          = ∑ x ∈ C, ∑ y ∈ C, ∑ j : ι, (if x j ≠ y j then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              exact hdist x y
        _ = ∑ x ∈ C, ∑ j : ι, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              exact Finset.sum_comm
        _ = ∑ j : ι, ∑ x ∈ C, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0) := Finset.sum_comm
    rw [hstep1]
    have hcoord : ∀ j : ι, ∑ x ∈ C, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0) =
        (M : ℝ) ^ 2 - ∑ σ, (m j σ) ^ 2 := by
      intro j
      have htot : ∑ x ∈ C, ∑ y ∈ C,
          ((if x j ≠ y j then (1 : ℝ) else 0) + (if x j = y j then (1 : ℝ) else 0)) = (M : ℝ) ^ 2 := by
        have hone : ∀ x : ι → Fin q, ∀ y : ι → Fin q,
            ((if x j ≠ y j then (1 : ℝ) else 0) + (if x j = y j then (1 : ℝ) else 0)) = 1 := by
          intro x y
          by_cases h : x j = y j <;> simp [h]
        simp only [hone, Finset.sum_const, nsmul_eq_mul, mul_one, hM]
        ring
      have hsplit : ∑ x ∈ C, ∑ y ∈ C,
          ((if x j ≠ y j then (1 : ℝ) else 0) + (if x j = y j then (1 : ℝ) else 0))
          = ∑ x ∈ C, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0)
            + ∑ x ∈ C, ∑ y ∈ C, (if x j = y j then (1 : ℝ) else 0) := by
        simp only [Finset.sum_add_distrib]
      have hagree : ∑ x ∈ C, ∑ y ∈ C, (if x j = y j then (1 : ℝ) else 0) = ∑ σ, (m j σ) ^ 2 := by
        have hinner : ∀ x : ι → Fin q, ∑ y ∈ C, (if x j = y j then (1 : ℝ) else 0) = m j (x j) := by
          intro x
          rw [Finset.sum_boole]
          have hfe : C.filter (fun y => x j = y j) = C.filter (fun y => y j = x j) := by
            apply Finset.filter_congr
            intro y _
            exact eq_comm
          rw [hfe]
        simp only [hinner]
        have hfib := Finset.sum_fiberwise_of_maps_to (s := C) (t := Finset.univ) (g := fun x => x j)
          (fun i _ => Finset.mem_univ _) (fun x => m j (x j))
        rw [← hfib]
        apply Finset.sum_congr rfl
        intro σ _
        have hconst : ∀ x ∈ C.filter (fun x => x j = σ), m j (x j) = m j σ := by
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((C.filter (fun x => x j = σ)).card : ℝ) = m j σ := rfl
        rw [hcard]
        ring
      linarith
    calc ∑ j : ι, ∑ x ∈ C, ∑ y ∈ C, (if x j ≠ y j then (1 : ℝ) else 0)
        = ∑ j : ι, ((M : ℝ) ^ 2 - ∑ σ, (m j σ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            exact hcoord j
      _ ≤ ∑ _j : ι, ((M : ℝ) ^ 2 - (M : ℝ) ^ 2 / (q : ℝ)) := by
            apply Finset.sum_le_sum
            intro j _
            linarith [hcs j]
      _ = (Fintype.card ι : ℝ) * ((M : ℝ) ^ 2 - (M : ℝ) ^ 2 / (q : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hmain : (M : ℝ) * ((M : ℝ) - 1) * d ≤
      (Fintype.card ι : ℝ) * ((M : ℝ) ^ 2 - (M : ℝ) ^ 2 / (q : ℝ)) := le_trans hlow hupper
  have h1 : ((M : ℝ) - 1) * d ≤
      (Fintype.card ι : ℝ) * ((M : ℝ) * ((q : ℝ) - 1) / (q : ℝ)) := by
    have heq : (Fintype.card ι : ℝ) * ((M : ℝ) ^ 2 - (M : ℝ) ^ 2 / (q : ℝ))
        = (M : ℝ) * ((Fintype.card ι : ℝ) * ((M : ℝ) * ((q : ℝ) - 1) / (q : ℝ))) := by
      field_simp
    rw [heq] at hmain
    have hmain' : (M : ℝ) * (((M : ℝ) - 1) * d) ≤
        (M : ℝ) * ((Fintype.card ι : ℝ) * ((M : ℝ) * ((q : ℝ) - 1) / (q : ℝ))) := by
      nlinarith [hmain]
    exact le_of_mul_le_mul_left hmain' hMpos
  have h2 : (M : ℝ) * ((q : ℝ) * d - ((q : ℝ) - 1) * (Fintype.card ι)) ≤ (q : ℝ) * d := by
    have hmul := mul_le_mul_of_nonneg_right h1 hqpos.le
    have heq : (Fintype.card ι : ℝ) * ((M : ℝ) * ((q : ℝ) - 1) / (q : ℝ)) * (q : ℝ)
        = (Fintype.card ι : ℝ) * (M : ℝ) * ((q : ℝ) - 1) := by
      field_simp
    rw [heq] at hmul
    nlinarith [hmul]
  rw [le_div_iff₀ hden]
  exact h2

/-- The chain of `2k+1` sets gives a contradiction. -/
lemma code_step {n p k : ℕ} (hk1 : 1 ≤ k)
    (Sig : Type*) [Fintype Sig] (hSig : Fintype.card Sig = k)
    (α : (S : Finset (Fin n)) → p + 1 ≤ S.card → (i : Fin n) → i ∈ S → Sig)
    (Sq : Fin (2 * k + 1) → Finset (Fin n))
    (hmono : StrictMono Sq)
    (hcard : ∀ i, (Sq i).card = p + 1 + i.val)
    (hsep : ∀ i j, i < j → p < (Finset.univ.filter (fun x : Fin n =>
      ∃ (h1 : x ∈ Sq i) (h2 : x ∈ Sq j),
        α (Sq i) (by have := hcard i; omega) x h1 ≠
        α (Sq j) (by have := hcard j; omega) x h2)).card)
    (hp2 : 2 * k * k ≤ p) (hp3 : 4 * k ^ 3 < (k + 1) * p + k + 1) :
    False := by
  classical
  let A : Finset (Fin n) := Sq 0
  have hAcard : A.card = p + 1 := by
    have h := hcard 0
    simpa [A] using h
  have hAsub : ∀ i : Fin (2 * k + 1), A ⊆ Sq i := by
    intro i
    exact hmono.monotone (Fin.zero_le i)
  let e : Sig ≃ Fin k := Fintype.equivFinOfCardEq hSig
  have hcard_le : ∀ i : Fin (2 * k + 1), p + 1 ≤ (Sq i).card := fun i => by
    rw [hcard i]; omega
  let v : Fin (2 * k + 1) → (A → Fin k) :=
    fun i x => e (α (Sq i) (hcard_le i) x.val (hAsub i x.property))
  have hD : ∀ i j : Fin (2 * k + 1), i < j → p + 1 - 2 * k ≤
      (Finset.univ.filter (fun x : A => v i x ≠ v j x)).card := by
    intro i j hij
    let D : Finset (Fin n) := Finset.univ.filter (fun x : Fin n =>
      ∃ (h1 : x ∈ Sq i) (h2 : x ∈ Sq j),
        α (Sq i) (hcard_le i) x h1 ≠ α (Sq j) (hcard_le j) x h2)
    have hDcard : p < D.card := hsep i j hij
    have hDsub : D ⊆ Sq i := by
      intro x hx
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.choose
    have hDA : (D ∩ A).card + (D \ A).card = D.card := Finset.card_inter_add_card_sdiff D A
    have hDAsub : D \ A ⊆ Sq i \ A := by
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨hDsub hx.1, hx.2⟩
    have hdA : (D \ A).card ≤ i.val := by
      calc (D \ A).card ≤ (Sq i \ A).card := Finset.card_le_card hDAsub
        _ = (Sq i).card - A.card := by
            have hAI : A ∩ Sq i = A := by
              ext x
              simp only [Finset.mem_inter]
              exact ⟨fun h => h.1, fun h => ⟨h, hAsub i h⟩⟩
            rw [Finset.card_sdiff, hAI]
        _ = i.val := by
            rw [hcard i, hAcard]
            omega
    have hge : p + 1 - 2 * k ≤ (D ∩ A).card := by
      have hi : i.val ≤ 2 * k := by have := i.isLt; omega
      omega
    have hbij : (Finset.univ.filter (fun x : A => v i x ≠ v j x)).card = (D ∩ A).card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_inter, D, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨hAsub i x.property, hAsub j x.property, ?_⟩, x.property⟩
        intro hcon
        exact hx (by simp only [v]; rw [hcon])
      · intro x _ y _ h
        exact Subtype.ext h
      · intro b hb
        simp only [Finset.mem_inter, D, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hcon
        rcases hb.1 with ⟨h1, h2, hne⟩
        exact hne (e.injective hcon)
    omega
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have hcontr : ∀ {i j : Fin (2 * k + 1)}, i < j → v i = v j → False := by
      intro i j hlt heq
      have hd := hD i j hlt
      have hempty : (Finset.univ.filter (fun x : A => v i x ≠ v j x)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ hx
        exact hx (by rw [heq])
      rw [hempty] at hd
      have hpos : 0 < p + 1 - 2 * k := by
        have h2k : 2 * k ≤ p := by
          have h1 : 2 * k ≤ (2 * k) * k := Nat.le_mul_of_pos_right (2 * k) hk1
          exact le_trans h1 hp2
        omega
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact hcontr h hij
    · exact hcontr h hij.symm
  let C : Finset (A → Fin k) := Finset.univ.image v
  have hCcard : C.card = 2 * k + 1 := by
    rw [show C = Finset.univ.image v from rfl, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  have hdistC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (p + 1 - 2 * k) ≤
      (Finset.univ.filter (fun j : A => x j ≠ y j)).card := by
    intro x hx y hy hxy
    simp only [C, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i ≠ j := by
      intro h
      exact hxy (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · exact hD i j h
    · have hji := hD j i h
      have hfil : (Finset.univ.filter (fun t : A => v i t ≠ v j t))
          = (Finset.univ.filter (fun t : A => v j t ≠ v i t)) := by
        apply Finset.filter_congr
        intro t _
        exact ne_comm
      rw [hfil]
      exact hji
  have hcardA : (Fintype.card A : ℝ) = (p : ℝ) + 1 := by
    rw [Fintype.card_coe, hAcard]
    push_cast
    ring
  have hdval : ((p + 1 - 2 * k : ℕ) : ℝ) = (p : ℝ) + 1 - 2 * (k : ℝ) := by
    have hle : 2 * k ≤ p + 1 := by nlinarith [hp2, hk1]
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hden : 0 < (k : ℝ) * ((p + 1 - 2 * k : ℕ) : ℝ) -
      ((k : ℝ) - 1) * (Fintype.card A) := by
    rw [hcardA, hdval]
    have h2k : 2 * (k : ℝ) ^ 2 ≤ (p : ℝ) := by
      have h' : ((2 * k * k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      push_cast at h'
      nlinarith
    nlinarith
  have hplot := plotkin_bound hk1 C (by omega) hCcard hdistC hden
  have hlt : (k : ℝ) * ((p + 1 - 2 * k : ℕ) : ℝ) /
      ((k : ℝ) * ((p + 1 - 2 * k : ℕ) : ℝ) - ((k : ℝ) - 1) * (Fintype.card A)) <
      ((2 * k + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hden]
    rw [hcardA, hdval]
    have hpk : 4 * (k : ℝ) ^ 3 < ((k : ℝ) + 1) * (p : ℝ) + (k : ℝ) + 1 := by
      exact_mod_cast hp3
    push_cast
    nlinarith
  linarith



/-- Target B: the generalized agreement lemma. -/
theorem generalized_agreement_lemma :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ n p : ℕ, 1 ≤ p → p ≤ n →
      ∀ (Sig : Type*) [Fintype Sig],
      ∀ α : (S : Finset (Fin n)) → (i : Fin n) → i ∈ S → Sig,
      ∀ ℓ : ℕ, a * Real.sqrt p ≤ ℓ →
      ∀ Sq : Fin ℓ → Finset (Fin n), StrictMono Sq →
        (∀ i : Fin ℓ, (Sq i).card = p + (i.val + 1)) →
        (∀ i j : Fin ℓ, i < j →
          p < (Finset.univ.filter (fun t : Fin n => ∃ (hti : t ∈ Sq i) (htj : t ∈ Sq j),
            α (Sq i) t hti ≠ α (Sq j) t htj)).card) →
        c * Real.sqrt p ≤ (Fintype.card Sig : ℝ) := by
  intro a ha
  refine ⟨min (a / 3) (1 / 2), ?_, ?_⟩
  · positivity
  intro n p hp1 hpn Sig _ α ℓ hℓ Sq hmono hcard hsep
  set c : ℝ := min (a / 3) (1 / 2) with hc
  have hc_le_a : c ≤ a / 3 := min_le_left _ _
  have hc_le_half : c ≤ 1 / 2 := min_le_right _ _
  have hc_pos : 0 < c := by positivity
  have hsp_nonneg : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp1
  -- if the alphabet is empty, the colouring cannot exist
  by_cases hk0 : Fintype.card Sig = 0
  · have hSig_empty : Fintype.card Sig = 0 := hk0
    have hℓ1 : 1 ≤ ℓ := by
      have : (0 : ℝ) < (ℓ : ℝ) := by
        have ha_sqrt : 0 < a * Real.sqrt p := mul_pos ha (Real.sqrt_pos.mpr hp_pos)
        linarith
      exact_mod_cast this
    have hi0 : Fin ℓ := ⟨0, by omega⟩
    have hne : (Sq hi0).Nonempty := by
      rw [← Finset.card_pos]
      have h := hcard hi0
      have : 0 < (Sq hi0).card := by rw [h]; omega
      simpa using this
    obtain ⟨t, ht⟩ := hne
    have : (α (Sq hi0) t ht) ∈ (Finset.univ : Finset Sig) := Finset.mem_univ _
    have huniv : (Finset.univ : Finset Sig) = ∅ := by
      rw [← Finset.card_eq_zero]; simpa using hSig_empty
    rw [huniv] at this
    simp at this
  · have hk1 : 1 ≤ Fintype.card Sig := Nat.one_le_iff_ne_zero.mpr hk0
    have hk1R : (1 : ℝ) ≤ (Fintype.card Sig : ℝ) := by exact_mod_cast hk1
    by_cases hcase : ℓ ≤ 2 * Fintype.card Sig + 1
    · -- the chain is short: length bound gives the result
      by_cases hsp : Real.sqrt p ≤ 3 / a
      · have ha3 : (0 : ℝ) < a / 3 := by positivity
        have h1 : c * Real.sqrt p ≤ 1 := by
          calc c * Real.sqrt p ≤ (a / 3) * (3 / a) := by
                apply mul_le_mul hc_le_a hsp hsp_nonneg (le_of_lt ha3)
            _ = 1 := by field_simp
        linarith
      · push_neg at hsp
        have hsp' : 3 ≤ a * Real.sqrt p := by
          have h := mul_lt_mul_of_pos_right hsp ha
          rw [div_mul_cancel₀ _ ha.ne'] at h
          nlinarith
        have hlen : (ℓ : ℝ) ≤ 2 * (Fintype.card Sig : ℝ) + 1 := by exact_mod_cast hcase
        have hk_ge : (a / 3) * Real.sqrt p ≤ (Fintype.card Sig : ℝ) := by
          nlinarith [hℓ, hlen, hsp', hsp_nonneg]
        calc c * Real.sqrt p ≤ (a / 3) * Real.sqrt p := by
              apply mul_le_mul_of_nonneg_right hc_le_a hsp_nonneg
          _ ≤ (Fintype.card Sig : ℝ) := hk_ge
    · -- the chain is long: truncate to `2k+1` sets and apply the code step
      push_neg at hcase
      have hkpos : (0 : ℝ) < (Fintype.card Sig : ℝ) := by exact_mod_cast hk1
      have hℓ_large : 2 * Fintype.card Sig + 1 < ℓ := hcase
      let α' : (S : Finset (Fin n)) → p + 1 ≤ S.card → (i : Fin n) → i ∈ S → Sig :=
        fun S _ i hi => α S i hi
      let Sq' : Fin (2 * Fintype.card Sig + 1) → Finset (Fin n) :=
        fun i => Sq ⟨i.val, by have := i.isLt; omega⟩
      have hmono' : StrictMono Sq' := by
        intro i j hij
        have hij' : (⟨i.val, by have := i.isLt; omega⟩ : Fin ℓ) <
            ⟨j.val, by have := j.isLt; omega⟩ := by
          simp only [Fin.lt_def]
          exact hij
        exact hmono hij' 
      have hcard' : ∀ i, (Sq' i).card = p + 1 + i.val := by
        intro i
        have h := hcard ⟨i.val, by have := i.isLt; omega⟩
        simp only [Sq']
        rw [h]
        simp only [Fin.val_mk]
        omega
      have hsep' : ∀ i j : Fin (2 * Fintype.card Sig + 1), i < j → p <
          (Finset.univ.filter (fun x : Fin n =>
            ∃ (h1 : x ∈ Sq' i) (h2 : x ∈ Sq' j),
              α' (Sq' i) (by have := hcard' i; omega) x h1 ≠
              α' (Sq' j) (by have := hcard' j; omega) x h2)).card := by
        intro i j hij
        have hij' : (⟨i.val, by have := i.isLt; omega⟩ : Fin ℓ) <
            ⟨j.val, by have := j.isLt; omega⟩ := by
          simp only [Fin.lt_def]; omega
        have h := hsep ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ hij'
        simpa [Sq', α'] using h
      by_cases hp2 : 2 * Fintype.card Sig * Fintype.card Sig ≤ p
      · by_cases hp3 : 4 * Fintype.card Sig ^ 3 < (Fintype.card Sig + 1) * p + Fintype.card Sig + 1
        · exact absurd (code_step hk1 Sig rfl α' Sq' hmono' hcard' hsep' hp2 hp3) (by simp)
        · -- `hp3` fails: the alphabet is large
          push_neg at hp3
          have hp3R : (4 : ℝ) * (Fintype.card Sig : ℝ) ^ 3 ≥
              ((Fintype.card Sig : ℝ) + 1) * (p : ℝ) + (Fintype.card Sig : ℝ) + 1 := by
            have h : ((4 * Fintype.card Sig ^ 3 : ℕ) : ℝ) ≥
                (((Fintype.card Sig + 1) * p + Fintype.card Sig + 1 : ℕ) : ℝ) := by
              exact_mod_cast hp3
            push_cast at h
            linarith
          have hp_le : (p : ℝ) ≤ 4 * (Fintype.card Sig : ℝ) ^ 2 := by
            nlinarith [hp3R, hk1R, hp_pos]
          -- √p ≤ 2k, hence √p/2 ≤ k
          have hsqrt_le : Real.sqrt p ≤ 2 * (Fintype.card Sig : ℝ) := by
            rw [Real.sqrt_le_iff]
            refine ⟨by linarith, ?_⟩
            nlinarith [hp_le]
          calc c * Real.sqrt p ≤ (1 / 2) * Real.sqrt p := by
                apply mul_le_mul_of_nonneg_right hc_le_half hsp_nonneg
            _ ≤ (Fintype.card Sig : ℝ) := by linarith
      · -- `hp2` fails: the alphabet is large
        push_neg at hp2
        have hp2R : (p : ℝ) < 2 * (Fintype.card Sig : ℝ) ^ 2 := by
          have h : ((2 * Fintype.card Sig * Fintype.card Sig : ℕ) : ℝ) > (p : ℝ) := by
            exact_mod_cast hp2
          push_cast at h
          nlinarith
        have h2pos : (0 : ℝ) ≤ 2 * (Fintype.card Sig : ℝ) ^ 2 := by positivity
        have hsqrt2 : Real.sqrt (2 * (Fintype.card Sig : ℝ) ^ 2) =
            Real.sqrt 2 * (Fintype.card Sig : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by positivity)]
        have hlt : Real.sqrt p < Real.sqrt 2 * (Fintype.card Sig : ℝ) := by
          rw [← hsqrt2]
          exact Real.sqrt_lt_sqrt (by positivity) hp2R
        have h2lt : Real.sqrt 2 < 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hk_ge : Real.sqrt p / 2 ≤ (Fintype.card Sig : ℝ) := by
          nlinarith [hlt, h2lt, hk1R]
        calc c * Real.sqrt p ≤ (1 / 2) * Real.sqrt p := by
              apply mul_le_mul_of_nonneg_right hc_le_half hsp_nonneg
          _ = Real.sqrt p / 2 := by ring
          _ ≤ (Fintype.card Sig : ℝ) := hk_ge

end PlotkinProbe


open Classical in
theorem solution :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ n p : ℕ, 1 ≤ p → p ≤ n →
      ∀ (Sig : Type*) [Fintype Sig],
      ∀ α : (S : Finset (Fin n)) → (i : Fin n) → i ∈ S → Sig,
      ∀ ℓ : ℕ, a * Real.sqrt p ≤ ℓ →
      ∀ Sq : Fin ℓ → Finset (Fin n), StrictMono Sq →
        (∀ i : Fin ℓ, (Sq i).card = p + (i.val + 1)) →
        (∀ i j : Fin ℓ, i < j →
          p < (Finset.univ.filter (fun t : Fin n => ∃ (hti : t ∈ Sq i) (htj : t ∈ Sq j),
            α (Sq i) t hti ≠ α (Sq j) t htj)).card) →
        c * Real.sqrt p ≤ (Fintype.card Sig : ℝ) :=
  PlotkinProbe.generalized_agreement_lemma
