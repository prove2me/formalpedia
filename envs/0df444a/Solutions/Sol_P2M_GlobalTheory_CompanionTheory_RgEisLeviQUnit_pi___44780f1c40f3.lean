-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:55.810501+00:00
-- url     : https://prove2.me/submissions/54ab49f1-ff5c-4ef3-a524-25949406b1a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_Tri_of_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (hi : Function.Injective A.i) (q : A.uQ ε s) (hq : (q : A.U ε ι) ∈ A.uΓ ε ι) :
    piQ A ε hσ q ∈ A.uΓ ε ↥sᶜ := by
  obtain ⟨g₀, hg⟩ := Subgroup.mem_subgroupOf.1 hq
  have e1 : ((g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E)).map A.i = ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    congrArg Units.val hg
  have e2 : (((g₀⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E)).map A.i =
      ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    rw [← hg, ← map_inv]
    rfl
  have t1 : Tri s (g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) := Tri.of_map A.i hi (e1 ▸ q_tri A ε hσ q)
  have t2 : Tri s ((g₀⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E) := Tri.of_map A.i hi (e2 ▸ q_tri' A ε hσ q)
  refine Subgroup.mem_subgroupOf.2 ⟨piG g₀ t1 t2, Units.ext ?_⟩
  change ((g₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E).submatrix (emb s) (emb s)).map A.i =
    ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).submatrix (emb s) (emb s)
  rw [← e1]
  rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
