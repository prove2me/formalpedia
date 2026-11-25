-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.closure_prop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:16.619524+00:00
-- url     : https://prove2.me/submissions/add6c0d1-4eb6-4abc-bfa8-d0df959b6898

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_one
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_one
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLe_of_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_mul_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_mul_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLe_add_lt
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_pair
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_pairing
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_op_one
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_eq_opL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution (hC : CompSt) (ε : Fin m → Bool) {x : Sym m n}
    (hx : x ∈ Submonoid.closure (Set.range fun ab : Fin m × Fin m => pairSym (n := n) ε ab.1 ab.2)) :
    ∃ d, EtaEq x d ∧ SymbolInFirstFamily ε x ∧ ∃ w ∈ PA (n := n) ε, ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r d ∧ ∀ f, w f = op (x + r) f := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨_, etaEq_pair ε ab.1 ab.2, symmetric_filtration_pairing ε ab.1 ab.2, opL (pairSym ε ab.1 ab.2),
      Algebra.subset_adjoin ⟨ab, rfl⟩, 0, symmetric_filtration_zero ε, etaLt_zero _, fun f => by rw [add_zero, op_eq_opL]⟩
  | one => exact ⟨0, etaEq_one, symmetric_filtration_one ε, 1, Subalgebra.one_mem _, 0, symmetric_filtration_zero ε, etaLt_zero _,
      fun f => by rw [add_zero, op_one]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d₁, he₁, hs₁, w₁, hw₁, r₁, hr₁, hl₁, hf₁⟩ := hx
    obtain ⟨d₂, he₂, hs₂, w₂, hw₂, r₂, hr₂, hl₂, hf₂⟩ := hy
    obtain ⟨r₀, hr₀, hl₀, hf₀⟩ := hC m n ε (x + r₁) (y + r₂) d₁ d₂ (symmetric_filtration_add hs₁ hr₁) (symmetric_filtration_add hs₂ hr₂)
      (etaLe_add_lt (etaLe_of_eq he₁) hl₁) (etaLe_add_lt (etaLe_of_eq he₂) hl₂)
    refine ⟨d₁ + d₂, etaEq_mul he₁ he₂, symmetric_filtration_mul hs₁ hs₂, w₁ * w₂, Subalgebra.mul_mem _ hw₁ hw₂,
      x * r₂ + r₁ * y + r₁ * r₂ + r₀, ?_, ?_, fun f => ?_⟩
    · exact symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_mul hs₁ hr₂) (symmetric_filtration_mul hr₁ hs₂)) (symmetric_filtration_mul hr₁ hr₂)) hr₀
    · refine etaLt_add (etaLt_add (etaLt_add (etaLt_mul_left (etaLe_of_eq he₁) hl₂)
        (etaLt_mul_right hl₁ (etaLe_of_eq he₂))) ?_) hl₀
      exact etaLt_mono (etaLt_mul_right hl₁ (fun t ht => (hl₂ t ht).le)) le_rfl
    · rw [Module.End.mul_apply, hf₂, hf₁, hf₀, ← op_add]
      congr 1; ring
end PositivityTheory.Rg.Sw.LC.B3
