-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:53.603305+00:00
-- url     : https://prove2.me/submissions/4179eb29-48f8-48c4-834c-bf7ff35ea170

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__Xlast_pow_mul_monomial_6ca4897b8fd3
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_emb_inj
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_kill_freezeSub
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_aeval_scaled_monomial
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
private theorem fin_castSucc_ne_last (i : Fin N) : Fin.castSucc i ≠ Fin.last N :=
  (Fin.castSucc_lt_last i).ne
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
private theorem homogeneousComponent_monomial_eq_ite (t : ℕ) (u : σ →₀ ℕ) (a : K) :
    homogeneousComponent t (monomial u a : MvPolynomial σ K) = if t = u.degree then monomial u a else 0 := by
  exact homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial a rfl))
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
private theorem llPart_mapDomain_emb (m : Fin N × Fin r →₀ ℕ) :
    llPart (Finsupp.mapDomain emb m) = m := by
  ext ⟨i, c⟩
  rw [llPart_apply]
  exact Finsupp.mapDomain_apply emb_inj m (i, c)
private theorem etaPart_mapDomain_emb (m : Fin N × Fin r →₀ ℕ) :
    etaPart (Finsupp.mapDomain emb m) = 0 := by
  ext c
  rw [etaPart_apply]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, c'⟩, h⟩
  simp [emb, fin_castSucc_ne_last i] at h
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
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (t : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (aeval (freezeSub p LL ρ) f) = homogeneousComponent t f := by
  rw [← coeffη_kill,
    show kill p ρ (aeval (Formalism.GM.M.freezeSub p LL ρ) f) =
      ((kill p ρ).comp (aeval (Formalism.GM.M.freezeSub p LL ρ))) f from rfl,
    kill_freezeSub]
  refine MvPolynomial.induction_on' f (fun m a => ?_) (fun f g hf hg => ?_)
  · rw [aeval_scaled_monomial, coeffη_Xlast_pow_mul_monomial, etaPart_mapDomain_emb,
      llPart_mapDomain_emb, zero_add, homogeneousComponent_monomial_eq_ite]
    have key : (Finsupp.single ρ m.degree = Finsupp.single ρ t) ↔ t = m.degree :=
      ⟨fun h' => (Finsupp.single_injective ρ h').symm, fun h' => by rw [h']⟩
    exact if_congr key rfl rfl
  · simp only [map_add, hf, hg]
end Formalism.GM.FrozenVariableComponents
