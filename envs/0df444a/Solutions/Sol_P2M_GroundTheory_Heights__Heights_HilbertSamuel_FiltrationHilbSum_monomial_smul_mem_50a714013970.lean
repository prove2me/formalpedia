-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.04114+00:00
-- url     : https://prove2.me/submissions/90a712e7-d794-410d-9fde-288cf428acfb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
theorem _root_.solution (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) (a : F)
    {m : K → ℤ} {y : M} (hy : y ∈ piece m) :
    (monomial d a : MRing ι F) • y ∈
      piece (m + fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) := by
  induction d using Finsupp.induction generalizing m y with
  | zero =>
    have h0 : (fun k => ((Finsupp.weight (blockWeight ι) (0 : (Σ k, ι k) →₀ ℕ)) k : ℤ)) = 0 := by
      funext k
      simp
    rw [h0, add_zero, ← C_apply, ← algebraMap_eq, algebraMap_smul]
    exact (piece m).smul_mem a hy
  | single_add v k d' _ _ ih =>
    have hpow : ∀ (e : ℕ) (m' : K → ℤ) (z : M), z ∈ piece m' →
        (X v ^ e : MRing ι F) • z ∈ piece (m' + e • unitDeg v.1) := by
      intro e
      induction e with
      | zero => intro m' z hz; simpa using hz
      | succ e ihe =>
        intro m' z hz
        rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
        exact hM.smul_mem v _ _ (ihe m' z hz)
    rw [monomial_single_add, mul_smul]
    have h2 := hpow k _ _ (ih hy)
    convert h2 using 2
    funext k'
    simp only [map_add, Finsupp.weight_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul, blockWeight, unitDeg, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
