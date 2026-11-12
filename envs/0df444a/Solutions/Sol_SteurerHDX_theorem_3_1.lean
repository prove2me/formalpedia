-- Prove2me | solution 1 for SteurerHDX.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:19:11.794064+00:00
-- url     : https://prove2.me/submissions/5f4b7514-04de-4d5c-9502-562275c6070e

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_spectralGap
import Definitions.Def_SteurerHDX_downUp
import Theorems.Thm_SteurerHDX_eq_3_1
import Theorems.Thm_SteurerHDX_lemma_2_1

section
set_option autoImplicit false
namespace SteurerHDX.Dev.T31
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

lemma sum_erase_eq (hd : 0 < d) (τ σ : Finset V) (hτ : τ.card = d) (g : Finset V → ℝ) :
    (∑ v ∈ τ, if τ.erase v ⊆ σ then g (τ.erase v) else 0) =
      ∑ S ∈ (τ ∩ σ).powersetCard (d - 1), g S := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun v _ => τ.erase v)
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_inter (Finset.erase_subset _ _) hv.2, ?_⟩
    rw [Finset.card_erase_of_mem hv.1, hτ]
  · intro v hv w hw h
    rw [Finset.mem_filter] at hv hw
    by_contra hne
    have : w ∈ τ.erase v := Finset.mem_erase.mpr ⟨Ne.symm hne, hw.1⟩
    rw [h] at this
    simp at this
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hSτ : S ⊆ τ := hS.1.trans Finset.inter_subset_left
    have hlt : S.card < τ.card := by omega
    obtain ⟨v, hvτ, hvS⟩ : ∃ v ∈ τ, v ∉ S := by
      by_contra hcon
      push_neg at hcon
      have := Finset.card_le_card (show τ ⊆ S from hcon)
      omega
    have hsub : S ⊆ τ.erase v := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hvS (h ▸ hx), hSτ hx⟩
    have heq : S = τ.erase v := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_erase_of_mem hvτ]; omega
    refine ⟨v, ?_, heq.symm⟩
    rw [Finset.mem_filter]
    refine ⟨hvτ, ?_⟩
    rw [← heq]
    exact hS.1.trans Finset.inter_subset_right
  · intro v hv
    rfl

lemma downUp_eq (hd : 0 < d) (τ σ : faces X d) : downUp X d τ σ =
    (1 / (d : ℝ)) * ∑ S ∈ (τ.1 ∩ σ.1).powersetCard (d - 1), 1 / (Nf X d S : ℝ) := by
  rw [downUp_apply, sum_erase_eq d hd τ.1 σ.1 (card_face X d τ) (fun S => 1 / (Nf X d S : ℝ))]

lemma downUp_symm (hd : 0 < d) (τ σ : faces X d) : downUp X d τ σ = downUp X d σ τ := by
  rw [downUp_eq X d hd, downUp_eq X d hd, Finset.inter_comm]

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

noncomputable def vec (i : faces X d) : EuclideanSpace ℝ (faces X 1) :=
  WithLp.toLp 2 (fun k => if k.1 ⊆ i.1 then 1 / Real.sqrt (d : ℝ) else 0)

lemma count_sub (hX : IsPure X d) (S : Finset V) (σ : Finset V) (hσ : σ ∈ X) (hS : S ⊆ σ) :
    ((Finset.univ : Finset (faces X 1)).filter (fun k => k.1 ⊆ S)).card = S.card := by
  symm
  refine Finset.card_bij (fun x hx => (⟨{x}, ?_⟩ : faces X 1)) ?_ ?_ ?_
  · simp only [faces, Finset.mem_filter]
    exact ⟨hX.1 σ hσ _ (by simpa using hS hx), by simp⟩
  · intro x hx
    simp [Finset.singleton_subset_iff, hx]
  · intro a ha b hb h
    simpa using congrArg Subtype.val h
  · intro k hk
    have hk1 : k.1.card = 1 := by
      have := k.2
      simp only [faces, Finset.mem_filter] at this
      exact this.2
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hk1
    have hkS : k.1 ⊆ S := by simpa using hk
    refine ⟨x, ?_, ?_⟩
    · exact hkS (by rw [hx]; simp)
    · apply Subtype.ext; simp [hx]

lemma inner_vec (hX : IsPure X d) (hd : 0 < d) (i j : faces X d) :
    inner ℝ (vec X d i) (vec X d j) = ((i.1 ∩ j.1).card : ℝ) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ∀ k : faces X 1, inner ℝ ((vec X d i) k) ((vec X d j) k) =
      if k.1 ⊆ i.1 ∩ j.1 then 1 / (d : ℝ) else 0 := by
    intro k
    simp only [vec, Finset.subset_inter_iff, real_inner_eq_re_inner, RCLike.inner_apply]
    by_cases a : k.1 ⊆ i.1 <;> by_cases b : k.1 ⊆ j.1 <;> simp [a, b]
    rw [← mul_inv, Real.mul_self_sqrt hdr.le]
  rw [PiLp.inner_apply]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    count_sub X d hX (i.1 ∩ j.1) i.1 (by have := i.2; simp only [faces, Finset.mem_filter] at this; exact this.1) Finset.inter_subset_left]
  field_simp

lemma norm_vec (hX : IsPure X d) (hd : 0 < d) (i : faces X d) : ‖vec X d i‖ = 1 := by
  have h := inner_vec X d hX hd i i
  rw [Finset.inter_self, card_face X d i, real_inner_self_eq_norm_sq] at h
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : ‖vec X d i‖ ^ 2 = 1 := by rw [h]; field_simp
  have := norm_nonneg (vec X d i)
  nlinarith

lemma dist_vec (hX : IsPure X d) (hd : 0 < d) (i j : faces X d) :
    ‖vec X d i - vec X d j‖ ^ 2 = 2 - 2 * ((i.1 ∩ j.1).card : ℝ) / d := by
  rw [@norm_sub_sq_real, norm_vec X d hX hd, norm_vec X d hX hd, inner_vec X d hX hd]
  ring

lemma tri_card (i j k : faces X d) :
    (i.1 ∩ k.1).card + (k.1 ∩ j.1).card ≤ d + (i.1 ∩ j.1).card := by
  have h := Finset.card_union_add_card_inter (i.1 ∩ k.1) (k.1 ∩ j.1)
  have h1 : ((i.1 ∩ k.1) ∪ (k.1 ∩ j.1)).card ≤ d := by
    have hk := card_face X d k
    have : ((i.1 ∩ k.1) ∪ (k.1 ∩ j.1)).card ≤ k.1.card := Finset.card_le_card
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_left)
    omega
  have h2 : ((i.1 ∩ k.1) ∩ (k.1 ∩ j.1)).card ≤ (i.1 ∩ j.1).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    tauto
  omega


lemma sum_inter_le (i : faces X d) :
    ∑ j : faces X d, (i.1 ∩ j.1).card ≤ d * degree X d := by
  have h1 : ∀ j : faces X d, (i.1 ∩ j.1).card = ∑ x ∈ i.1, if x ∈ j.1 then 1 else 0 := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x ∈ i.1, ∑ j : faces X d, (if x ∈ j.1 then 1 else 0) ≤ degree X d := by
    intro x hx
    have : ∑ j : faces X d, (if x ∈ j.1 then 1 else 0) =
        ((faces X d).filter (fun σ => x ∈ σ)).card := by
      rw [Finset.sum_coe_sort (faces X d) (fun σ => if x ∈ σ then 1 else 0), ← Finset.sum_filter,
        Finset.sum_const, smul_eq_mul, mul_one]
    rw [this]
    unfold degree
    apply Finset.le_sup (f := fun x => ((faces X d).filter (fun σ => x ∈ σ)).card)
    have hi : i.1 ∈ X := by have := i.2; simp only [faces, Finset.mem_filter] at this; exact this.1
    exact Finset.mem_biUnion.mpr ⟨i.1, hi, hx⟩
  calc _ ≤ ∑ x ∈ i.1, degree X d := Finset.sum_le_sum h2
    _ = d * degree X d := by rw [Finset.sum_const, smul_eq_mul, card_face X d i]

lemma part_i (hX : IsPure X d) (hd : 0 < d) (hcard : 2 ≤ (faces X d).card) :
    (1 / ((faces X d).card : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (vec X d i) (vec X d j)| ≤
      (degree X d : ℝ) / (faces X d).card := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < (faces X d).card := by exact_mod_cast (by omega : 0 < (faces X d).card)
  have h1 : ∀ i j : faces X d, |inner ℝ (vec X d i) (vec X d j)| = ((i.1 ∩ j.1).card : ℝ) / d := by
    intro i j
    rw [inner_vec X d hX hd, abs_of_nonneg (by positivity)]
  simp only [h1]
  have h2 : ∀ i : faces X d, ∑ j : faces X d, ((i.1 ∩ j.1).card : ℝ) / d ≤ (degree X d : ℝ) := by
    intro i
    rw [← Finset.sum_div, div_le_iff₀ hdr]
    have := sum_inter_le X d i
    have h3 : (∑ j : faces X d, ((i.1 ∩ j.1).card : ℝ)) ≤ (d : ℝ) * degree X d := by exact_mod_cast this
    linarith
  have h3 : ∑ i : faces X d, ∑ j : faces X d, ((i.1 ∩ j.1).card : ℝ) / d ≤
      ∑ i : faces X d, (degree X d : ℝ) := Finset.sum_le_sum (fun i _ => h2 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at h3
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hn]
  nlinarith

lemma dirichlet_nonneg (hd : 0 < d) (f : faces X d → ℝ) :
    0 ≤ GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d)) f f := by
  unfold GibbsCongestion.dirichletForm
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro x _
  apply Finset.sum_nonneg; intro y _
  rw [walk_eq X d hd, statDist_eq X d hd]
  have := downUp_nonneg X d x y
  have : (0:ℝ) ≤ 1 / ((faces X d).card : ℝ) := by positivity
  have h := mul_self_nonneg (f x - f y)
  calc (0:ℝ) ≤ (1 / ((faces X d).card : ℝ) * downUp X d x y) * ((f x - f y) * (f x - f y)) := by positivity
    _ = _ := by ring

lemma var_const (hd : 0 < d) (f : faces X d → ℝ) (h : ∀ x y, f x = f y) :
    variance (downUp X d) f = 0 := by
  unfold variance
  have : ∀ x y, (f x - f y) ^ 2 = 0 := fun x y => by rw [h x y]; simp
  simp [this]

lemma part_ii (hX : IsPure X d) (hd : 0 < d) (hcard : 2 ≤ (faces X d).card) (α : ℝ) (hα : 0 < α)
    (hgap : α / d ≤ spectralGap (downUp X d)) :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ A B : Finset (faces X d), Disjoint A B →
        β * (faces X d).card ≤ A.card → β * (faces X d).card ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖vec X d i - vec X d j‖ ^ 2 ≤ 2 / (β * Real.sqrt (α * d)) := by
  intro β hβ0 hβ1 A B hAB hA hB
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < (faces X d).card := by exact_mod_cast (by omega : 0 < (faces X d).card)
  have hAn : A.Nonempty := by
    apply Finset.card_pos.mp
    have : (0:ℝ) < A.card := lt_of_lt_of_le (by positivity) hA
    exact_mod_cast this
  have hBn : B.Nonempty := by
    apply Finset.card_pos.mp
    have : (0:ℝ) < B.card := lt_of_lt_of_le (by positivity) hB
    exact_mod_cast this
  have hs : 0 < Real.sqrt (α * d) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : Real.sqrt (α * d) * Real.sqrt (α * d) = α * d := Real.mul_self_sqrt (by positivity)
  set ε : ℝ := 1 / (β * Real.sqrt (α * d)) with hε
  have hεpos : 0 < ε := by positivity
  have hrhs : 2 / (β * Real.sqrt (α * d)) = 2 * ε := by rw [hε]; ring
  rw [hrhs]
  have hle2 : ∀ i j : faces X d, ‖vec X d i - vec X d j‖ ^ 2 ≤ 2 := by
    intro i j
    rw [dist_vec X d hX hd]
    have : (0:ℝ) ≤ ((i.1 ∩ j.1).card : ℝ) / d := by positivity
    have e : 2 * ((i.1 ∩ j.1).card : ℝ) / d = 2 * (((i.1 ∩ j.1).card : ℝ) / d) := by ring
    linarith
  by_cases hε1 : 1 ≤ ε
  · obtain ⟨i, hi⟩ := hAn
    obtain ⟨j, hj⟩ := hBn
    exact ⟨i, hi, j, hj, by linarith [hle2 i j]⟩
  · push Not at hε1
    by_contra hcon
    push Not at hcon
    have hsep : ∀ σ ∈ A, ∀ τ ∈ B, (((σ.1 ∩ τ.1).card : ℕ) : ℝ) < d * (1 - ε) := by
      intro σ hσ τ hτ
      have h := hcon σ hσ τ hτ
      rw [dist_vec X d hX hd] at h
      have e : 2 * ((σ.1 ∩ τ.1).card : ℝ) / d = 2 * (((σ.1 ∩ τ.1).card : ℝ) / d) := by ring
      have : ((σ.1 ∩ τ.1).card : ℝ) / d < 1 - ε := by linarith
      rw [div_lt_iff₀ hdr] at this
      linarith
    obtain ⟨δ₀, hδ₀, hδ⟩ := SteurerHDX.eq_3_1 X d hX hcard β ε hβ0 hβ1 hεpos hε1 A B hAB hA hB hsep
    have key := hδ (δ₀ / 2) (by positivity) (by linarith)
    set f := testFn X d A ε (δ₀ / 2) with hf
    set E := GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d)) f f with hE
    have hE0 : 0 ≤ E := dirichlet_nonneg X d hd f
    have hK : 0 < β ^ 2 * (ε * d) ^ 2 := by positivity
    have hVar : 0 < variance (downUp X d) f := lt_of_le_of_lt (by positivity) key
    have hnc : ∃ x y, f x ≠ f y := by
      by_contra hc
      push Not at hc
      have := var_const X d hd f hc
      linarith
    have hL := SteurerHDX.lemma_2_1 (downUp X d) (by rw [Fintype.card_coe]; exact hcard)
      (downUp_symm X d hd) (downUp_nonneg X d) (by intro x; rw [vdeg_one X d hd]; norm_num)
    have hmem := hL.2.2 ⟨f, hnc, rfl⟩
    have hgap' : α / d ≤ E / variance (downUp X d) f := by
      have : spectralGap (downUp X d) = 1 - lambdaTwo (downUp X d) := rfl
      linarith
    rw [le_div_iff₀ hVar] at hgap'
    have hprod : α / d * (β ^ 2 * (ε * d) ^ 2) = 1 := by
      rw [hε]
      field_simp
      nlinarith [hs2]
    have : E * (β ^ 2 * (ε * d) ^ 2) ≥ α / d * variance (downUp X d) f * (β ^ 2 * (ε * d) ^ 2) :=
      mul_le_mul_of_nonneg_right hgap' hK.le
    have e2 : α / d * variance (downUp X d) f * (β ^ 2 * (ε * d) ^ 2) = variance (downUp X d) f := by
      calc _ = (α / d * (β ^ 2 * (ε * d) ^ 2)) * variance (downUp X d) f := by ring
        _ = _ := by rw [hprod, one_mul]
    linarith

end SteurerHDX.Dev.T31

namespace SteurerHDX
open SteurerHDX.Dev.T31

theorem chk_theorem_3_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (α : ℝ)
    (hX : IsPure X d) (hcard : 2 ≤ (faces X d).card) (hα : 0 < α)
    (hgap : α / d ≤ spectralGap (downUp X d)) :
    ∃ v : faces X d → EuclideanSpace ℝ (faces X 1),
      (∀ i k, 0 ≤ v i k) ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ i j k, ‖v i - v j‖ ^ 2 ≤ ‖v i - v k‖ ^ 2 + ‖v k - v j‖ ^ 2) ∧
      (1 / ((faces X d).card : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v i) (v j)| ≤
        (degree X d : ℝ) / (faces X d).card ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ A B : Finset (faces X d), Disjoint A B →
        β * (faces X d).card ≤ A.card → β * (faces X d).card ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖v i - v j‖ ^ 2 ≤ 2 / (β * Real.sqrt (α * d)) := by
  have hd : 0 < d := d_pos X d hcard
  refine ⟨vec X d, ?_, norm_vec X d hX hd, ?_, part_i X d hX hd hcard, part_ii X d hX hd hcard α hα hgap⟩
  · intro i k
    simp only [vec]
    split_ifs <;> positivity
  · intro i j k
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    rw [dist_vec X d hX hd, dist_vec X d hX hd, dist_vec X d hX hd]
    have := tri_card X d i j k
    have h : ((i.1 ∩ k.1).card : ℝ) + ((k.1 ∩ j.1).card : ℝ) ≤ d + ((i.1 ∩ j.1).card : ℝ) := by exact_mod_cast this
    have e : ∀ c : ℝ, 2 * c / d = 2 * (c / d) := fun c => by ring
    rw [e, e, e]
    have : (((i.1 ∩ k.1).card : ℝ) + ((k.1 ∩ j.1).card : ℝ)) / d ≤ (d + ((i.1 ∩ j.1).card : ℝ)) / d :=
      div_le_div_of_nonneg_right h hdr.le
    rw [add_div, add_div, div_self hdr.ne'] at this
    linarith

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_theorem_3_1 := @SteurerHDX.chk_theorem_3_1
