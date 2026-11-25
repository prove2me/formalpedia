-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ker_relation_map_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:25.294014+00:00
-- url     : https://prove2.me/submissions/6599c345-6dc6-4d65-9c46-9ee3cca1a56d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_not_injective_of_trdeg_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) : RingHom.ker (d.relationEliminateColumn c) ≠ ⊥ := by
  intro hker
  have hinj : Function.Injective (d.relationEliminateColumn c) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  let g : Fin (d.D + 1) × Fin d.N → TVar d.D d.N := fun t => (t.1, (d.jc c).succAbove t.2)
  let φ : KTp K d.D d.N →ₐ[K] MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c) :=
    MvPolynomial.aeval fun t : TVar d.D d.N =>
      Fin.insertNth (α := fun _ => MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (t.1, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (t.1, k)) t.2
  have hfac : d.relationEliminateColumn c = ((MvPolynomial.rename g).restrictScalars K).comp φ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [Data.relationEliminateColumn, φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, MvPolynomial.aeval_X]
    by_cases hj : j = d.jc c
    · subst hj
      simp only [if_true, Fin.insertNth_apply_same, map_neg, map_sum, map_mul, MvPolynomial.rename_X,
        MvPolynomial.rename_C, g]
      congr 1
      have e1 := Finset.add_sum_erase Finset.univ (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (d.jc c)
      exact add_left_cancel (e1.trans e2)
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [if_neg hj, Fin.insertNth_apply_succAbove, MvPolynomial.rename_X, g]
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hinj
    rw [hfac, AlgHom.comp_apply, AlgHom.comp_apply, hab]
  refine not_injective_of_trdeg_lt φ d.D (hd.trdeg c) ?_ hφ
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega
end ReciprocityTheory.ChartRestriction.G.T0.Data
