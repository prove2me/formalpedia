-- Prove2me | solution 1 for SteurerHDX.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:52:48.979202+00:00
-- url     : https://prove2.me/submissions/b6c02497-af53-4c0b-ba5a-7afaf35541b0

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_downUp
import Definitions.Def_SteurerHDX_walk
import Definitions.Def_SteurerHDX_variance
import Definitions.Def_SteurerHDX_testFn
import Definitions.Def_GibbsCongestion_dirichletForm

section
set_option autoImplicit false
namespace SteurerHDX.Dev.E31
open SteurerHDX

variable {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)

lemma card_face (x : faces X d) : x.1.card = d := by
  have := x.2
  simp only [faces, Finset.mem_filter] at this
  exact this.2

noncomputable def Nf (S : Finset V) : ℕ := ((faces X d).filter (fun ρ => S ⊆ ρ)).card

lemma downUp_apply (τ σ : faces X d) : downUp X d τ σ =
    (1 / (d : ℝ)) * ∑ v ∈ τ.1, if τ.1.erase v ⊆ σ.1 then 1 / (Nf X d (τ.1.erase v) : ℝ) else 0 := rfl

lemma Nf_pos (τ : faces X d) (v : V) : 0 < Nf X d (τ.1.erase v) := by
  unfold Nf
  apply Finset.card_pos.mpr
  exact ⟨τ.1, Finset.mem_filter.mpr ⟨τ.2, Finset.erase_subset _ _⟩⟩

lemma d_pos (hcard : 2 ≤ (faces X d).card) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    subst h
    have : (faces X 0).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [faces, Finset.mem_filter] at ha hb
      rw [Finset.card_eq_zero.mp ha.2, Finset.card_eq_zero.mp hb.2]
    omega
  · exact h

lemma row_sum (hd : 0 < d) (τ : faces X d) : ∑ σ, downUp X d τ σ = 1 := by
  simp only [downUp_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ v ∈ τ.1, ∑ σ : faces X d, (if τ.1.erase v ⊆ σ.1 then 1 / (Nf X d (τ.1.erase v) : ℝ) else 0) = 1 := by
    intro v _
    rw [Finset.sum_coe_sort (faces X d) (fun ρ => if τ.1.erase v ⊆ ρ then 1 / (Nf X d (τ.1.erase v) : ℝ) else 0)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := Nf_pos X d τ v
    have h2 : ((faces X d).filter (fun ρ => τ.1.erase v ⊆ ρ)).card = Nf X d (τ.1.erase v) := rfl
    rw [h2]
    field_simp
  rw [Finset.sum_congr rfl h1]
  simp [card_face X d τ]
  field_simp

lemma downUp_nonneg (τ σ : faces X d) : 0 ≤ downUp X d τ σ := by
  rw [downUp_apply]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · positivity
  · exact le_refl _

lemma vdeg_one (hd : 0 < d) (τ : faces X d) : vdeg (downUp X d) τ = 1 := row_sum X d hd τ

lemma statDist_eq (hd : 0 < d) (x : faces X d) :
    statDist (downUp X d) x = 1 / ((faces X d).card : ℝ) := by
  unfold statDist
  simp [vdeg_one X d hd]

lemma walk_eq (hd : 0 < d) (x y : faces X d) : walk (downUp X d) x y = downUp X d x y := by
  simp [walk, vdeg_one X d hd]

lemma sdiff_card_eq (a b : Finset V) (h : a.card = b.card) : (a \ b).card = (b \ a).card := by
  have h1 := Finset.card_sdiff_add_card_inter a b
  have h2 := Finset.card_sdiff_add_card_inter b a
  rw [Finset.inter_comm] at h2
  omega

lemma adj_of_ne_zero (hd : 0 < d) (τ σ : faces X d) (h : downUp X d τ σ ≠ 0) :
    τ = σ ∨ (facetGraph X d).Adj τ σ := by
  rw [downUp_apply] at h
  have h1 : ∑ v ∈ τ.1, (if τ.1.erase v ⊆ σ.1 then 1 / (Nf X d (τ.1.erase v) : ℝ) else 0) ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  obtain ⟨v, hv, hv2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hsub : τ.1.erase v ⊆ σ.1 := by
    by_contra hn; apply hv2; simp [hn]
  by_cases hts : τ = σ
  · exact Or.inl hts
  right
  have hcτ := card_face X d τ
  have hcσ := card_face X d σ
  have heq := sdiff_card_eq τ.1 σ.1 (by rw [hcτ, hcσ])
  have hle : (τ.1 \ σ.1).card ≤ 1 := by
    have : τ.1 \ σ.1 ⊆ {v} := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_singleton]
      by_contra hne
      exact hx.2 (hsub (Finset.mem_erase.mpr ⟨hne, hx.1⟩))
    simpa using Finset.card_le_card this
  have hge : 1 ≤ (τ.1 \ σ.1).card := by
    by_contra hlt
    have h0 : (τ.1 \ σ.1).card = 0 := by omega
    have h0' : τ.1 \ σ.1 = ∅ := Finset.card_eq_zero.mp h0
    have : τ.1 ⊆ σ.1 := Finset.sdiff_eq_empty_iff_subset.mp h0'
    exact hts (Subtype.ext (Finset.eq_of_subset_of_card_le this (by rw [hcτ, hcσ])))
  show (τ.1 \ σ.1).card + (σ.1 \ τ.1).card = 2
  omega

lemma adj_card (σ τ : faces X d) (h : (facetGraph X d).Adj σ τ) : (σ.1 \ τ.1).card = 1 := by
  have heq := sdiff_card_eq σ.1 τ.1 (by rw [card_face X d σ, card_face X d τ])
  have h2 : (σ.1 \ τ.1).card + (τ.1 \ σ.1).card = 2 := h
  omega

lemma rho_triangle (x y z : Finset V) : (x \ z).card ≤ (x \ y).card + (y \ z).card := by
  have : x \ z ⊆ (x \ y) ∪ (y \ z) := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    by_cases hy : a ∈ y
    · right; exact ⟨hy, ha.2⟩
    · left; exact ⟨ha.1, hy⟩
  exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)

lemma rho_walk (x y : faces X d) (p : (facetGraph X d).Walk x y) :
    (x.1 \ y.1).card ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rename_i a b c
    have := rho_triangle a.1 b.1 c.1
    have h1 := adj_card X d a b h
    rw [SimpleGraph.Walk.length_cons]
    omega

lemma rho_edist (x y : faces X d) : (((x.1 \ y.1).card : ℕ) : ℕ∞) ≤ (facetGraph X d).edist x y := by
  by_cases hr : (facetGraph X d).Reachable x y
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    exact_mod_cast rho_walk X d x y p
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top


noncomputable def G (c δ : ℝ) (D : ℕ∞) : ℝ :=
  if D = ⊤ then 0 else max (1 + δ - (D.toNat : ℝ) / c) 0

lemma G_lip (c δ : ℝ) (hc : 0 < c) (D D' : ℕ∞) (h1 : D ≤ D' + 1) (h2 : D' ≤ D + 1) :
    |G c δ D - G c δ D'| ≤ 1 / c := by
  induction D using ENat.recTopCoe with
  | top =>
    induction D' using ENat.recTopCoe with
    | top => simp [G]; positivity
    | coe m' =>
      exfalso
      have : (⊤ : ℕ∞) ≤ ((m' + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      simp at this
  | coe m =>
    induction D' using ENat.recTopCoe with
    | top =>
      exfalso
      have : (⊤ : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      simp at this
    | coe m' =>
      have h1' : m ≤ m' + 1 := by exact_mod_cast h1
      have h2' : m' ≤ m + 1 := by exact_mod_cast h2
      simp only [G, ENat.coe_ne_top, if_false, ENat.toNat_coe]
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      have : (1 + δ - (m : ℝ) / c) - (1 + δ - (m' : ℝ) / c) = ((m' : ℝ) - m) / c := by ring
      rw [this, abs_div, abs_of_pos hc]
      apply div_le_div_of_nonneg_right _ hc.le
      rw [abs_le]
      have a1 : (m : ℝ) ≤ m' + 1 := by exact_mod_cast h1'
      have a2 : (m' : ℝ) ≤ m + 1 := by exact_mod_cast h2'
      constructor <;> linarith

noncomputable def Dist (A : Finset (faces X d)) (σ : faces X d) : ℕ∞ :=
  ⨅ a ∈ A, (facetGraph X d).edist σ a

lemma testFn_eq (A : Finset (faces X d)) (ε δ : ℝ) (σ : faces X d) :
    testFn X d A ε δ σ = G (ε * d) δ (Dist X d A σ) := rfl

lemma Dist_adj (A : Finset (faces X d)) (σ τ : faces X d) (h : (facetGraph X d).Adj σ τ) :
    Dist X d A σ ≤ Dist X d A τ + 1 := by
  unfold Dist
  simp only [ENat.iInf_add]
  refine le_iInf₂ fun a ha => ?_
  refine iInf₂_le_of_le a ha ?_
  calc (facetGraph X d).edist σ a ≤ (facetGraph X d).edist σ τ + (facetGraph X d).edist τ a :=
        SimpleGraph.edist_triangle
    _ = (facetGraph X d).edist τ a + 1 := by
        rw [SimpleGraph.edist_eq_one_iff_adj.mpr h, add_comm]

lemma testFn_lip (A : Finset (faces X d)) (ε δ : ℝ) (hc : 0 < ε * d) (σ τ : faces X d)
    (h : (facetGraph X d).Adj σ τ) :
    (testFn X d A ε δ σ - testFn X d A ε δ τ) ^ 2 ≤ (1 / (ε * d)) ^ 2 := by
  rw [testFn_eq, testFn_eq]
  have := G_lip (ε * d) δ hc _ _ (Dist_adj X d A σ τ h) (Dist_adj X d A τ σ h.symm)
  exact sq_le_sq' (by linarith [abs_le.mp this]) (abs_le.mp this).2

lemma testFn_A (A : Finset (faces X d)) (ε δ : ℝ) (hδ : 0 < δ) (σ : faces X d) (hσ : σ ∈ A) :
    testFn X d A ε δ σ = 1 + δ := by
  rw [testFn_eq]
  have : Dist X d A σ = 0 := by
    apply le_antisymm _ bot_le
    exact iInf₂_le_of_le σ hσ (by simp)
  simp [G, this]
  linarith

lemma testFn_B (A : Finset (faces X d)) (ε δ : ℝ) (hε : 0 < ε) (hd : 0 < d) (hδ : 0 < δ)
    (hδ0 : δ * (ε * d) < ((⌊ε * d⌋₊ + 1 : ℕ) : ℝ) - ε * d)
    (τ : faces X d)
    (hτ : ∀ a ∈ A, ε * d < (((a.1 \ τ.1).card : ℕ) : ℝ)) :
    testFn X d A ε δ τ = 0 := by
  have hc : 0 < ε * d := mul_pos hε (by exact_mod_cast hd)
  rw [testFn_eq]
  have hD : ((⌊ε * d⌋₊ + 1 : ℕ) : ℕ∞) ≤ Dist X d A τ := by
    refine le_iInf₂ fun a ha => ?_
    have h1 : ⌊ε * d⌋₊ < (a.1 \ τ.1).card := by
      rw [Nat.floor_lt hc.le]; exact hτ a ha
    have h2 := rho_edist X d a τ
    rw [SimpleGraph.edist_comm] at h2
    exact le_trans (by exact_mod_cast h1) h2
  unfold G
  split_ifs with hT
  · rfl
  · have hk : ((⌊ε * d⌋₊ + 1 : ℕ) : ℝ) ≤ ((Dist X d A τ).toNat : ℝ) := by
      have : ⌊ε * d⌋₊ + 1 ≤ (Dist X d A τ).toNat := by
        lift Dist X d A τ to ℕ using hT with k hk
        rw [ENat.toNat_natCast]
        exact_mod_cast hD
      exact_mod_cast this
    apply max_eq_right
    have : 1 + δ ≤ ((Dist X d A τ).toNat : ℝ) / (ε * d) := by
      rw [le_div_iff₀ hc]
      nlinarith
    linarith

end SteurerHDX.Dev.E31

namespace SteurerHDX
open SteurerHDX.Dev.E31

theorem chk_eq_3_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (hX : IsPure X d) (hcard : 2 ≤ (faces X d).card) (β ε : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (A B : Finset (faces X d)) (hAB : Disjoint A B)
    (hA : β * (faces X d).card ≤ A.card) (hB : β * (faces X d).card ≤ B.card)
    (hsep : ∀ σ ∈ A, ∀ τ ∈ B, (((σ.1 ∩ τ.1).card : ℕ) : ℝ) < d * (1 - ε)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d))
          (testFn X d A ε δ) (testFn X d A ε δ) * (β ^ 2 * (ε * d) ^ 2) <
        variance (downUp X d) (testFn X d A ε δ) := by
  have hd : 0 < d := d_pos X d hcard
  have hc : 0 < ε * d := mul_pos hε0 (by exact_mod_cast hd)
  have hm0 : ε * d < ((⌊ε * d⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  refine ⟨(((⌊ε * d⌋₊ + 1 : ℕ) : ℝ) - ε * d) / (ε * d), div_pos (by linarith) hc, ?_⟩
  intro δ hδ hδ1
  have hδ0 : δ * (ε * d) < ((⌊ε * d⌋₊ + 1 : ℕ) : ℝ) - ε * d := by
    rw [lt_div_iff₀ hc] at hδ1; exact hδ1
  set f := testFn X d A ε δ with hf
  set n : ℝ := ((faces X d).card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast (by omega : 0 < (faces X d).card)
  -- f on A and B
  have fA : ∀ σ ∈ A, f σ = 1 + δ := fun σ hσ => testFn_A X d A ε δ hδ σ hσ
  have fB : ∀ τ ∈ B, f τ = 0 := by
    intro τ hτ
    apply testFn_B X d A ε δ hε0 hd hδ hδ0 τ
    intro a ha
    have h1 := Finset.card_sdiff_add_card_inter a.1 τ.1
    rw [card_face X d a] at h1
    have h2 := hsep a ha τ hτ
    have h3 : (((a.1 \ τ.1).card : ℕ) : ℝ) + ((a.1 ∩ τ.1).card : ℕ) = d := by exact_mod_cast h1
    nlinarith
  -- variance lower bound
  have hvar : β ^ 2 * (1 + δ) ^ 2 / 2 ≤ variance (downUp X d) f := by
    unfold variance
    simp only [statDist_eq X d hd]
    have hnn : ∀ x y : faces X d, 0 ≤ 1 / n * (1 / n) * (f x - f y) ^ 2 := fun x y => by positivity
    have h1 : ∑ x ∈ A, ∑ y ∈ B, 1 / n * (1 / n) * (f x - f y) ^ 2 ≤
        ∑ x, ∑ y, 1 / n * (1 / n) * (f x - f y) ^ 2 := by
      calc ∑ x ∈ A, ∑ y ∈ B, 1 / n * (1 / n) * (f x - f y) ^ 2
          ≤ ∑ x ∈ A, ∑ y, 1 / n * (1 / n) * (f x - f y) ^ 2 := by
            apply Finset.sum_le_sum; intro x _
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hnn x y)
        _ ≤ ∑ x, ∑ y, 1 / n * (1 / n) * (f x - f y) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun x _ _ => Finset.sum_nonneg (fun y _ => hnn x y))
    have h2 : ∑ x ∈ A, ∑ y ∈ B, 1 / n * (1 / n) * (f x - f y) ^ 2 =
        (A.card : ℝ) * B.card * (1 / n * (1 / n) * (1 + δ) ^ 2) := by
      rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => by
        rw [fA x hx, fB y hy]; try simp))]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : β ^ 2 * n ^ 2 ≤ (A.card : ℝ) * B.card := by
      have : (β * n) * (β * n) ≤ (A.card : ℝ) * B.card :=
        mul_le_mul hA hB (by positivity) (by positivity)
      nlinarith
    have h4 : β ^ 2 * (1 + δ) ^ 2 ≤ (A.card : ℝ) * B.card * (1 / n * (1 / n) * (1 + δ) ^ 2) := by
      have : (A.card : ℝ) * B.card * (1 / n * (1 / n) * (1 + δ) ^ 2) =
          ((A.card : ℝ) * B.card) / n ^ 2 * (1 + δ) ^ 2 := by field_simp
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [le_div_iff₀ (by positivity)]; exact h3
    linarith
  -- Dirichlet bound
  have hE : GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d)) f f ≤
      (1 / 2) * (1 / (ε * d)) ^ 2 := by
    unfold GibbsCongestion.dirichletForm
    simp only [statDist_eq X d hd, walk_eq X d hd]
    have hterm : ∀ x y : faces X d, 1 / n * downUp X d x y * (f x - f y) * (f x - f y) ≤
        1 / n * downUp X d x y * (1 / (ε * d)) ^ 2 := by
      intro x y
      by_cases h0 : downUp X d x y = 0
      · simp [h0]
      · have hW := downUp_nonneg X d x y
        have : (f x - f y) * (f x - f y) ≤ (1 / (ε * d)) ^ 2 := by
          rcases adj_of_ne_zero X d hd x y h0 with h | h
          · subst h; simp; positivity
          · rw [← sq]; exact testFn_lip X d A ε δ hc x y h
        calc 1 / n * downUp X d x y * (f x - f y) * (f x - f y)
            = 1 / n * downUp X d x y * ((f x - f y) * (f x - f y)) := by ring
          _ ≤ 1 / n * downUp X d x y * (1 / (ε * d)) ^ 2 :=
            mul_le_mul_of_nonneg_left this (by positivity)
    have hsum : ∑ x, ∑ y, 1 / n * downUp X d x y * (1 / (ε * d)) ^ 2 = (1 / (ε * d)) ^ 2 := by
      have : ∀ x : faces X d, ∑ y, 1 / n * downUp X d x y * (1 / (ε * d)) ^ 2 =
          1 / n * (1 / (ε * d)) ^ 2 := by
        intro x
        rw [← Finset.sum_mul, ← Finset.mul_sum, row_sum X d hd x]; ring
      rw [Finset.sum_congr rfl (fun x _ => this x)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [← hn]; field_simp
    have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hterm x y))
    rw [hsum] at this
    linarith
  have hb : 0 < β ^ 2 := by positivity
  have key : GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d)) f f *
      (β ^ 2 * (ε * d) ^ 2) ≤ β ^ 2 / 2 := by
    calc _ ≤ (1 / 2) * (1 / (ε * d)) ^ 2 * (β ^ 2 * (ε * d) ^ 2) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ = β ^ 2 / 2 := by field_simp
  have h1 : 1 < (1 + δ) ^ 2 := by nlinarith
  have : β ^ 2 / 2 < β ^ 2 * (1 + δ) ^ 2 / 2 := by nlinarith [mul_lt_mul_of_pos_left h1 hb]
  linarith

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_eq_3_1 := @SteurerHDX.chk_eq_3_1
