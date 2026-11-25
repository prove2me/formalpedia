-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:09.257788+00:00
-- url     : https://prove2.me/submissions/362dfd86-c04a-40e1-9297-91fd7a87e44b

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_parts
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
section
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Parts
variable {N r : ℕ}
end Parts
section Coeff
variable {K : Type*} [CommRing K] {N r : ℕ}
private theorem coeff_coeffη_eq_coeff_comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff m (coeffη b F) = coeff (comb b m) F := by
  refine MvPolynomial.induction_on' F (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_monomial]
    by_cases h : etaPart n = b
    · have key : llPart n = m ↔ n = comb b m :=
        ⟨fun h' => by rw [← h, ← h', comb_parts],
         fun h' => by rw [h', llPart_comb]⟩
      rw [if_pos h, coeff_monomial, coeff_monomial]
      exact if_congr key rfl rfl
    · rw [if_neg h, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h (etaPart_comb b m)
  · simp only [map_add, coeff_add, hp, hq]
end Coeff
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Coeff2
variable {K : Type*} [CommRing K] {N r : ℕ}
end Coeff2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Gl
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Gl
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type*} [CommRing K] {σ : Type*}
end Ops
section Rest
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Rest
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Freeze
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Freeze
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Base
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Base
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Pol
variable {K : Type*} [CommRing K]
end Pol
section Pol2
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Pol2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.FrozenVariableComponents
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
variable {K : Type*} [CommRing K] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff m (coeffη b F) = coeff (comb b m) F :=
  coeff_coeffη_eq_coeff_comb b m F
end Formalism.GM.FrozenVariableComponents
