-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithVar_proof_4a52428ded73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:58.912795+00:00
-- url     : https://prove2.me/submissions/eefc6a7a-666d-4eaa-9340-b2ea2b4ce742

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open DualArithmeticVariety
namespace GroundTheory.Heights₂.Heights
namespace DualArithVar
theorem _root_.solution (h : CoordConeArithVar.Statement) : DualArithVar.Statement := by
  intro K _ _ i F T _ _ b hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K fun t => (b t : Fin (n + 1) → K)
  rw [span_basis b] at hsp
  let B : Module.Basis κ K (Fin (n + 1) → K) := Module.Basis.mk hli hsp.ge
  let e : Fin (n + 1) ≃ κ := (B.indexEquiv (Pi.basisFun K (Fin (n + 1)))).symm
  let u : Fin (n + 1) → T := a ∘ e
  let w : Fin (n + 1) → ProjField K (n + 1) := fun l => evalForm (n + 1) (b (u l) : Fin (n + 1) → K)
  let s : Fin n → ProjField K (n + 1) := fun l => w l.succ / w 0
  let v : Fin (n + 1) → ProjField K (n + 1) := Fin.cons (w 0) s
  have hy := dualLatticeCoord_eq b
  have hw0 : w 0 ≠ 0 := evalForm_ne_zero (hli.ne_zero (e 0))
  have hspw : ∀ ψ, evalForm (n + 1) ψ ∈ Submodule.span K (Set.range w) := by
    intro ψ
    have hψ : ψ ∈ Submodule.span K (Set.range (((fun t => (b t : Fin (n + 1) → K)) ∘ a) ∘ e)) := by
      rw [EquivLike.range_comp, hsp]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := evalForm (n + 1)) hψ
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hwE : ∀ l, w l ∈ IntermediateField.adjoin K (Set.range v) := by
    intro l
    have hv : ∀ l, v l ∈ IntermediateField.adjoin K (Set.range v) :=
      fun l => IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
    induction l using Fin.cases with
    | zero => exact hv 0
    | succ m =>
      have := mul_mem (hv m.succ) (hv 0)
      simpa [v, s, div_mul_cancel₀ _ hw0] using this
  have hall : ∀ z, z ∈ IntermediateField.adjoin K (Set.range v) := by
    refine mem_of_gen_mem _ fun j => ?_
    have hX : algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j) =
        evalForm (n + 1) (Pi.single j 1) := by
      rw [evalForm, Fintype.linearCombination_apply_single, one_smul]
    rw [hX]
    exact (Submodule.span_le (p := (IntermediateField.adjoin K (Set.range v)).toSubalgebra.toSubmodule)).mpr
      (by rintro _ ⟨l, rfl⟩; exact hwE l) (hspw _)
  have hv : AlgebraicIndependent K v := by
    have := isAlgebraic_of_adjoin _ hall
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K v (trdeg_eq (n + 1)).le).1
  have hs : AlgebraicIndependent ℚ s :=
    (hv.comp Fin.succ (Fin.succ_injective _)).restrictScalars (algebraMap ℚ K).injective
  have hint : ∀ z ∈ Submodule.span K (Set.range w),
      IsIntegral (IntermediateField.adjoin ℚ (Set.range s)) (z / w 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      induction l using Fin.cases with
      | zero => rw [div_self hw0]; exact isIntegral_one
      | succ m =>
        exact isIntegral_algebraMap (x := (⟨s m, IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩⟩ :
          IntermediateField.adjoin ℚ (Set.range s)))
    | zero => rw [zero_div]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [add_div]; exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, mul_div_assoc]
      exact ((Algebra.IsIntegral.isIntegral (R := ℚ) c).map
        (IsScalarTower.toAlgHom ℚ K (ProjField K (n + 1)))).tower_top.mul hx
  refine h Unit (dualBlocks T) (ProjField K (n + 1)) (dualLatticeCoord b) (fun _ => u 0) n s ⟨()⟩
    (fun _ => by rw [hy]; exact hw0) hs (fun l => IntermediateField.subset_adjoin _ _ ⟨⟨(), u l.succ⟩, ?_⟩) ?_
  · show dualLatticeCoord b ⟨(), u l.succ⟩ / dualLatticeCoord b ⟨(), u 0⟩ = w l.succ / w 0
    rw [hy, hy]
  · rintro r ⟨⟨⟨⟩, t⟩, rfl⟩
    show IsAlgebraic _ (dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), u 0⟩)
    rw [hy, hy]
    exact (hint _ (hspw _)).isAlgebraic
end DualArithVar
end GroundTheory.Heights₂.Heights
