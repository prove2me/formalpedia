-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:02.108693+00:00
-- url     : https://prove2.me/submissions/7be35cec-14a7-49c8-8669-f688e57cffdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus
namespace GroundTheory.Heights₂.Heights.IncidenceZeroLocus
theorem _root_.solution {K ρ κ : Type*} [Field K] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] (A : Matrix ρ κ K)
    (hA : ∀ f, Pi.single f 1 ∈ Submodule.span K (Set.range A.col)) :
    ∃ e : ρ → κ, (A.submatrix id e).det ≠ 0 := by
  have htop : Submodule.span K (Set.range A.col) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K ρ).span_eq, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    simpa using hA f
  obtain ⟨κ', a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  have : Finite κ' := Finite.of_injective a ha
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ρ = Fintype.card κ' := by
    rw [← Module.finrank_fintype_fun_eq_card K, Module.finrank_eq_card_basis b]
  let eqv := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ eqv, ?_⟩
  have hli' : LinearIndependent K (A.submatrix id (a ∘ eqv)).col :=
    hli.comp eqv eqv.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hli'
  exact hli'
end GroundTheory.Heights₂.Heights.IncidenceZeroLocus
