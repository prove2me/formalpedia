-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.genericHomAt_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:19.427802+00:00
-- url     : https://prove2.me/submissions/0f86a903-7e6d-46a8-84a1-2b073011868b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_w_eq_scalarRatio_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hw0 : d.w j0 c ≠ 0)
    (hq : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))
    (i : Fin (d.D + 1)) (hi : i ≠ 0) :
    d.sH c (X (i, j0)) = -∑ j ∈ Finset.univ.erase j0, d.sH c (X (i, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dif_pos hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have hq0 : q j0 ≠ 0 := by
    intro h0
    apply hw0
    rw [hx j0, h0, zero_smul]
  have hxq : ∀ k, d.x c k = q ((d.jc c).succAbove k) := fun k => hqdef _
  obtain ⟨T, hTdef⟩ : ∃ T : Fin (d.N + 1) → OmS (Ω c) d.D d.N, ∀ j, d.sH c (X (i, j)) = T j :=
    ⟨_, fun _ => rfl⟩
  have hTX : ∀ j, T j = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (Sum.inr (i, k))) j) := by
    intro j
    rw [← hTdef]
    simp only [Data.sH, sHom, MvPolynomial.aeval_X, sImg, if_neg hi]
  have hCr : ∀ a : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (MvPolynomial.C a) =
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N),
      MvPolynomial.algebraMap_eq]
  have hTjc : T (d.jc c) = -∑ k, T ((d.jc c).succAbove k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    simp only [map_neg, map_sum, map_mul, hCr]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hsum : ∑ j, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) = 0 := by
    rw [Fin.sum_univ_succAbove _ (d.jc c), hq1, map_one, mul_one, hTjc]
    simp only [hxq]
    exact neg_add_cancel _
  simp only [hq, hqdef, hTdef, map_div₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)] at hsum
  have hr0 : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) ≠ 0 := (map_ne_zero _).mpr hq0
  have hS : ∑ j ∈ Finset.univ.erase j0, T j * (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0)) =
      (∑ j ∈ Finset.univ.erase j0, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j)) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hS, ← neg_div, eq_div_iff hr0]
  linear_combination hsum
end ReciprocityTheory.ChartRestriction.G.T0.Data
