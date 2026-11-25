-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__Xlast_pow_mul_monomial_6ca4897b8fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:23.663493+00:00
-- url     : https://prove2.me/submissions/a84f96bd-237f-4256-9ead-e076a7f585f5

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7
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
private theorem llPart_add (m m' : Fin (N + 1) × Fin r →₀ ℕ) : llPart (m + m') = llPart m + llPart m' := by
  ext x
  simp
private theorem etaPart_add (m m' : Fin (N + 1) × Fin r →₀ ℕ) :
    etaPart (m + m') = etaPart m + etaPart m' := by
  ext c
  simp
private theorem llPart_single_last (c : Fin r) (k : ℕ) :
    llPart (Finsupp.single (Fin.last N, c) k) = 0 := by
  ext ⟨i', c'⟩
  simp
private theorem etaPart_single_last (c : Fin r) (k : ℕ) :
    etaPart (Finsupp.single (Fin.last N, c) k) = Finsupp.single c k := by
  ext c'
  simp [Finsupp.single_apply]
end Parts
section Coeff
variable {K : Type*} [CommRing K] {N r : ℕ}
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
theorem _root_.solution (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (a : K) :
    coeffη b (X (Fin.last N, ρ) ^ k * monomial m a) =
      if etaPart m + Finsupp.single ρ k = b then monomial (llPart m) a else 0 := by
  rw [X_pow_mul_monomial', coeffη_monomial, etaPart_add, llPart_add, etaPart_single_last,
    llPart_single_last, add_zero]
end Formalism.GM.FrozenVariableComponents
