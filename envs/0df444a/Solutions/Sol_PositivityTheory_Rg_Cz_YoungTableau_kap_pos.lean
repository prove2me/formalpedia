-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.kap_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:35.103458+00:00
-- url     : https://prove2.me/submissions/5760b885-242e-446c-bab6-4f2bdb274d3e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


section
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace YoungTableau
section Pos
variable {n N : ℕ} {ι : Type} [DecidableEq ι] {C : Type} [DecidableEq C]
private theorem sum_sum_ite_mul_eq_sum_mul_comp {Γ : Type} [Fintype Γ] [DecidableEq Γ] {κ : Type} (s : Finset κ)
    (x : κ → Γ) (w : κ → ℤ) (F : Γ → ℤ) :
    ∑ g, (∑ i ∈ s, if x i = g then w i else 0) * F g = ∑ i ∈ s, w i * F (x i) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
private theorem sum_closed_eq_sum_left_mul {Γ : Type} [Group Γ] [DecidableEq Γ] (C : Finset Γ)
    (hCm : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C) (hCi : ∀ x ∈ C, x⁻¹ ∈ C) {a : Γ} (ha : a ∈ C)
    (F : Γ → ℤ) : ∑ x ∈ C, F x = ∑ u ∈ C, F (a * u) := by
  apply Finset.sum_nbij' (fun x => a⁻¹ * x) (fun u => a * u)
  · intro x hx
    exact hCm _ (hCi _ ha) _ hx
  · intro u hu
    exact hCm _ ha _ hu
  · intro x _
    simp
  · intro u _
    simp
  · intro x _
    simp
private theorem sum_closed_eq_sum_mul_right {Γ : Type} [Group Γ] [DecidableEq Γ] (C : Finset Γ)
    (hCm : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C) (hCi : ∀ x ∈ C, x⁻¹ ∈ C) {a : Γ} (ha : a ∈ C)
    (F : Γ → ℤ) : ∑ x ∈ C, F x = ∑ v ∈ C, F (v * a) := by
  apply Finset.sum_nbij' (fun x => x * a⁻¹) (fun v => v * a)
  · intro x hx
    exact hCm _ hx _ (hCi _ ha)
  · intro u hu
    exact hCm _ hu _ ha
  · intro x _
    simp
  · intro u _
    simp
  · intro x _
    simp
private theorem sum_ite_mul_mul_eq_pos_of_subgroup_transversal {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] (C R : Finset Γ)
    (e : Γ → ℤ) (hC1 : (1 : Γ) ∈ C) (hCm : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C)
    (hCi : ∀ x ∈ C, x⁻¹ ∈ C) (hR1 : (1 : Γ) ∈ R) (hRC : ∀ x ∈ R, x ∈ C → x = 1)
    (he : e 1 = 1) :
    0 < ∑ b1 ∈ R, ∑ u ∈ C, ∑ b2 ∈ R, ∑ v ∈ C,
      if u * b2 * v = b1 then e b1 * e b2 else 0 := by
  set K := ∑ b1 ∈ R, ∑ u ∈ C, ∑ b2 ∈ R, ∑ v ∈ C,
      (if u * b2 * v = b1 then e b1 * e b2 else 0) with hK
  let f : Γ → ℤ := fun g => ∑ t ∈ C ×ˢ (R ×ˢ C), if t.1 * t.2.1 * t.2.2 = g then e t.2.1 else 0
  have hI : ∀ a1 ∈ C, ∀ b1 : Γ, ∀ a1' ∈ C,
      (∑ a2 ∈ C, ∑ b2 ∈ R, ∑ a2' ∈ C,
        if a2 * b2 * a2' = a1 * b1 * a1' then e b1 * e b2 else 0) =
      ∑ u ∈ C, ∑ b2 ∈ R, ∑ v ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0 := by
    intro a1 ha1 b1 a1' ha1'
    rw [sum_closed_eq_sum_left_mul C hCm hCi ha1]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun b2 _ => ?_
    rw [sum_closed_eq_sum_mul_right C hCm hCi ha1']
    refine Finset.sum_congr rfl fun v _ => ?_
    have hm : a1 * u * b2 * (v * a1') = a1 * (u * b2 * v) * a1' := by simp only [mul_assoc]
    simp only [hm, mul_left_inj, mul_right_inj]
  have h1 : ∑ g, f g * f g = (C.card : ℤ) * C.card * K := by
    have h0 := sum_sum_ite_mul_eq_sum_mul_comp (C ×ˢ (R ×ˢ C)) (fun t => t.1 * t.2.1 * t.2.2) (fun t => e t.2.1) f
    rw [show (∑ g, f g * f g) = ∑ i ∈ C ×ˢ (R ×ˢ C), e i.2.1 * f (i.1 * i.2.1 * i.2.2) from h0]
    simp only [f, Finset.mul_sum, Finset.sum_product, mul_ite, mul_zero]
    rw [Finset.sum_congr rfl fun a1 ha1 => Finset.sum_congr rfl fun b1 _ =>
      Finset.sum_congr rfl fun a1' ha1' => hI a1 ha1 b1 a1' ha1']
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hK]
    ring
  have h2 : f 1 = C.card := by
    simp only [f, Finset.sum_product]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single (1 : Γ)]
    · rw [Finset.sum_eq_single a⁻¹]
      · simp [he]
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        rw [mul_one] at h
        exact eq_inv_of_mul_eq_one_right h
      · intro h
        exact absurd (hCi a ha) h
    · intro b hb hb1
      apply Finset.sum_eq_zero
      intro a' ha'
      rw [if_neg]
      intro h
      apply hb1
      apply hRC b hb
      have hb' : b = a⁻¹ * (a * b * a') * a'⁻¹ := by simp [mul_assoc]
      rw [h, mul_one] at hb'
      rw [hb']
      exact hCm _ (hCi _ ha) _ (hCi _ ha')
    · intro h
      exact absurd hR1 h
  have h3 : f 1 * f 1 ≤ ∑ g, f g * f g :=
    Finset.single_le_sum (f := fun g => f g * f g) (fun g _ => mul_self_nonneg (f g))
      (Finset.mem_univ 1)
  have hc : (0 : ℤ) < C.card := by exact_mod_cast Finset.card_pos.2 ⟨1, hC1⟩
  have hcc : (0 : ℤ) < (C.card : ℤ) * C.card := mul_pos hc hc
  rw [h1, h2] at h3
  by_contra hK0
  push_neg at hK0
  have := mul_nonpos_of_nonneg_of_nonpos hcc.le hK0
  linarith
private theorem sum_ite_mul_inv_mem_eq_sum_mul {Γ : Type} [Group Γ] [DecidableEq Γ] (G R : Finset Γ) (p : Γ)
    (hp : ∀ b ∈ R, b * p ∈ G) (F : Γ → ℤ) :
    ∑ σ ∈ G, (if σ * p⁻¹ ∈ R then F σ else 0) = ∑ b ∈ R, F (b * p) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun σ => σ * p⁻¹) (fun b => b * p)
  · intro σ hσ
    exact (Finset.mem_filter.1 hσ).2
  · intro b hb
    exact Finset.mem_filter.2 ⟨hp b hb, by simpa using hb⟩
  · intro σ _
    simp
  · intro b _
    simp
  · intro σ _
    simp
private theorem sum_e_mul_prod_sums_eq_four_sum {Γ : Type} [Group Γ] [DecidableEq Γ] (G C R : Finset Γ) (e : Γ → ℤ)
    (hem : ∀ x y, e (x * y) = e x * e y) (hee : ∀ x, e x * e x = 1)
    (hCG : ∀ x ∈ C, x ∈ G) (hRG : ∀ x ∈ R, x ∈ G) (hGm : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hCi : ∀ x ∈ C, x⁻¹ ∈ C) :
    ∑ σ ∈ G, e σ * ((∑ π ∈ C, if σ * π⁻¹ ∈ R then e π else 0) *
      (∑ ρ ∈ R, if σ * ρ⁻¹ ∈ C then e ρ else 0)) =
    ∑ b1 ∈ R, ∑ u ∈ C, ∑ b2 ∈ R, ∑ v ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0 := by
  have hu : ∀ b1 b2 v : Γ, (∑ u ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0) =
      if b1 * (b2 * v)⁻¹ ∈ C then e b1 * e b2 else 0 := by
    intro b1 b2 v
    have h : ∀ u, (u * b2 * v = b1) ↔ (u = b1 * (b2 * v)⁻¹) := fun u => by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc]
    simp only [h]
    exact Finset.sum_ite_eq' _ _ _
  have hinv : ∀ x : Γ, x ∈ C ↔ x⁻¹ ∈ C := fun x => ⟨hCi x, fun h => by simpa using hCi _ h⟩
  calc ∑ σ ∈ G, e σ * ((∑ π ∈ C, if σ * π⁻¹ ∈ R then e π else 0) *
        (∑ ρ ∈ R, if σ * ρ⁻¹ ∈ C then e ρ else 0))
      = ∑ σ ∈ G, ∑ π ∈ C, ∑ ρ ∈ R,
          if σ * π⁻¹ ∈ R then (if σ * ρ⁻¹ ∈ C then e σ * e π * e ρ else 0) else 0 := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        split_ifs <;> ring
    _ = ∑ π ∈ C, ∑ σ ∈ G, ∑ ρ ∈ R,
          if σ * π⁻¹ ∈ R then (if σ * ρ⁻¹ ∈ C then e σ * e π * e ρ else 0) else 0 :=
        Finset.sum_comm
    _ = ∑ π ∈ C, ∑ ρ ∈ R, ∑ σ ∈ G,
          if σ * π⁻¹ ∈ R then (if σ * ρ⁻¹ ∈ C then e σ * e π * e ρ else 0) else 0 :=
        Finset.sum_congr rfl fun π _ => Finset.sum_comm
    _ = ∑ π ∈ C, ∑ ρ ∈ R, ∑ b2 ∈ R,
          if b2 * π * ρ⁻¹ ∈ C then e (b2 * π) * e π * e ρ else 0 := by
        refine Finset.sum_congr rfl fun π hπ => Finset.sum_congr rfl fun ρ _ => ?_
        exact sum_ite_mul_inv_mem_eq_sum_mul G R π (fun b hb => hGm _ (hRG b hb) _ (hCG π hπ))
          (fun σ => if σ * ρ⁻¹ ∈ C then e σ * e π * e ρ else 0)
    _ = ∑ π ∈ C, ∑ ρ ∈ R, ∑ b2 ∈ R, if ρ * (b2 * π)⁻¹ ∈ C then e ρ * e b2 else 0 := by
        refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun b2 _ => ?_
        have hc : (b2 * π * ρ⁻¹ ∈ C) ↔ (ρ * (b2 * π)⁻¹ ∈ C) := by
          rw [hinv (b2 * π * ρ⁻¹)]
          simp [_root_.mul_inv_rev, mul_assoc]
        by_cases h : ρ * (b2 * π)⁻¹ ∈ C
        · rw [if_pos (hc.2 h), if_pos h, hem]
          linear_combination (e b2 * e ρ) * hee π
        · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
    _ = ∑ v ∈ C, ∑ b1 ∈ R, ∑ b2 ∈ R, if b1 * (b2 * v)⁻¹ ∈ C then e b1 * e b2 else 0 := rfl
    _ = ∑ b1 ∈ R, ∑ v ∈ C, ∑ b2 ∈ R, if b1 * (b2 * v)⁻¹ ∈ C then e b1 * e b2 else 0 :=
        Finset.sum_comm
    _ = ∑ b1 ∈ R, ∑ b2 ∈ R, ∑ v ∈ C, if b1 * (b2 * v)⁻¹ ∈ C then e b1 * e b2 else 0 :=
        Finset.sum_congr rfl fun b1 _ => Finset.sum_comm
    _ = ∑ b1 ∈ R, ∑ b2 ∈ R, ∑ v ∈ C, ∑ u ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0 := by
        simp only [hu]
    _ = ∑ b1 ∈ R, ∑ b2 ∈ R, ∑ u ∈ C, ∑ v ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0 :=
        Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun b2 _ => Finset.sum_comm
    _ = ∑ b1 ∈ R, ∑ u ∈ C, ∑ b2 ∈ R, ∑ v ∈ C, if u * b2 * v = b1 then e b1 * e b2 else 0 :=
        Finset.sum_congr rfl fun b1 _ => Finset.sum_comm
end Pos
end YoungTableau
end PositivityTheory.Rg.Cz
end
end

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n N : ℕ} {ι : Type} [DecidableEq ι] {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (tl : Fin N → ι) (colF colS : Fin N → C) (r c : Fin N → Fin n)
    (hF : ∀ k k', colF k = colF k' ↔ tl k = tl k' ∧ c k = c k')
    (hS : ∀ k k', colS k = colS k' ↔ tl k = tl k' ∧ r k = r k')
    (hinj : ∀ k k', tl k = tl k' → r k = r k' → c k = c k' → k = k') : 0 < kap tl colF colS r c := by
  have hGt : ∀ x ∈ colG tl, ∀ p, tl (x p) = tl p := fun x hx => (mem_colG tl x).1 hx
  have hCG : ∀ x ∈ colG colF, x ∈ colG tl := fun x hx =>
    (mem_colG tl x).2 fun p => ((hF (x p) p).1 ((mem_colG colF x).1 hx p)).1
  have hRG : ∀ x ∈ colG colS, x ∈ colG tl := fun x hx =>
    (mem_colG tl x).2 fun p => ((hS (x p) p).1 ((mem_colG colS x).1 hx p)).1
  have hP : ∀ σ ∈ colG tl, ∀ π ∈ colG colF, (r ∘ ⇑π = r ∘ ⇑σ ↔ σ * π⁻¹ ∈ colG colS) := by
    intro σ hσ π hπ
    rw [mem_colG]
    constructor
    · intro h p
      have e1 := congrFun h (π⁻¹ p)
      simp only [Function.comp_apply] at e1
      rw [show π (π⁻¹ p) = p by simp] at e1
      rw [hS, Equiv.Perm.mul_apply]
      refine ⟨?_, e1.symm⟩
      rw [hGt σ hσ, hGt _ (hCG _ (colG_inv' colF hπ))]
    · intro h
      funext k
      have e2 := (hS _ _).1 (h (π k))
      rw [Equiv.Perm.mul_apply, show π⁻¹ (π k) = k by simp] at e2
      exact e2.2.symm
  have hQ : ∀ σ ∈ colG tl, ∀ ρ ∈ colG colS, (c ∘ ⇑ρ = c ∘ ⇑σ ↔ σ * ρ⁻¹ ∈ colG colF) := by
    intro σ hσ ρ hρ
    rw [mem_colG]
    constructor
    · intro h p
      have e1 := congrFun h (ρ⁻¹ p)
      simp only [Function.comp_apply] at e1
      rw [show ρ (ρ⁻¹ p) = p by simp] at e1
      rw [hF, Equiv.Perm.mul_apply]
      refine ⟨?_, e1.symm⟩
      rw [hGt σ hσ, hGt _ (hRG _ (colG_inv' colS hρ))]
    · intro h
      funext k
      have e2 := (hF _ _).1 (h (ρ k))
      rw [Equiv.Perm.mul_apply, show ρ⁻¹ (ρ k) = k by simp] at e2
      exact e2.2.symm
  have key : kap tl colF colS r c = ∑ σ ∈ colG tl, (Equiv.Perm.sign σ : ℤ) *
      ((∑ π ∈ colG colF, if σ * π⁻¹ ∈ colG colS then (Equiv.Perm.sign π : ℤ) else 0) *
      (∑ ρ ∈ colG colS, if σ * ρ⁻¹ ∈ colG colF then (Equiv.Perm.sign ρ : ℤ) else 0)) := by
    unfold kap sg
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have a1 : (∑ π ∈ colG colF, if r ∘ ⇑π = r ∘ ⇑σ then (Equiv.Perm.sign π : ℤ) else 0) =
        ∑ π ∈ colG colF, if σ * π⁻¹ ∈ colG colS then (Equiv.Perm.sign π : ℤ) else 0 :=
      Finset.sum_congr rfl fun π hπ => by simp only [hP σ hσ π hπ]
    have a2 : (∑ ρ ∈ colG colS, if c ∘ ⇑ρ = c ∘ ⇑σ then (Equiv.Perm.sign ρ : ℤ) else 0) =
        ∑ ρ ∈ colG colS, if σ * ρ⁻¹ ∈ colG colF then (Equiv.Perm.sign ρ : ℤ) else 0 :=
      Finset.sum_congr rfl fun ρ hρ => by simp only [hQ σ hσ ρ hρ]
    rw [a1, a2]
  have hRC : ∀ x ∈ colG colS, x ∈ colG colF → x = 1 := by
    intro x hxS hxF
    refine Equiv.Perm.ext fun k => ?_
    rw [Equiv.Perm.one_apply]
    have h1 := (hS _ _).1 ((mem_colG colS x).1 hxS k)
    have h2 := (hF _ _).1 ((mem_colG colF x).1 hxF k)
    exact hinj _ _ h1.1 h1.2 h2.2
  rw [key]
  refine lt_of_lt_of_eq (sum_ite_mul_mul_eq_pos_of_subgroup_transversal (colG colF) (colG colS) (fun g => (Equiv.Perm.sign g : ℤ))
    ((mem_colG _ _).2 fun p => rfl) (fun x hx y hy => colG_mul' colF hx hy)
    (fun x hx => colG_inv' colF hx) ((mem_colG _ _).2 fun p => rfl) hRC (by simp))
    (sum_e_mul_prod_sums_eq_four_sum (colG tl) (colG colF) (colG colS) (fun g => (Equiv.Perm.sign g : ℤ))
      (fun x y => by simp [Equiv.Perm.sign_mul])
      (fun x => by
        rw [← Units.val_mul, Int.units_mul_self, Units.val_one])
      hCG hRG (fun x hx y hy => colG_mul' tl hx hy) (fun x hx => colG_inv' colF hx)).symm
end PositivityTheory.Rg.Cz.YoungTableau
