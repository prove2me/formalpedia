-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:05.535812+00:00
-- url     : https://prove2.me/submissions/f8c7ba8e-86cb-4c5d-be34-aaf743149877

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
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
private theorem kill_monomial_eq_ite (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    kill p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial m a else 0 := by
  classical
  rw [kill, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, Finsupp.prod, Finsupp.prod]
    refine congrArg (fun z => algebraMap ℚ_[p] (MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) a * z) ?_
    refine Finset.prod_congr rfl (fun w hw => ?_)
    try dsimp only
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply Finsupp.mem_support_iff.1 hw
    have h3 := h w.2 h2
    rw [← h1] at h3
    exact h3
  · push Not at h
    obtain ⟨c, hc, hm⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm), mul_zero]
    try dsimp only
    have hw : ((Fin.last N, c) : Fin (N + 1) × Fin r).1 = Fin.last N ∧
        ((Fin.last N, c) : Fin (N + 1) × Fin r).2 ≠ ρ := ⟨rfl, hc⟩
    rw [if_pos hw, zero_pow hm]
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
theorem _root_.solution (ρ : Fin r) (t : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (kill p ρ G) = coeffη (Finsupp.single ρ t) G := by
  refine MvPolynomial.induction_on' G (fun m a => ?_) (fun f g hf hg => ?_)
  · rw [kill_monomial_eq_ite]
    split_ifs with h
    · rfl
    · rw [map_zero, coeffη_monomial, if_neg]
      intro hm
      apply h
      intro c hc
      have := DFunLike.congr_fun hm c
      simpa [Finsupp.single_apply, Ne.symm hc] using this
  · simp only [map_add, hf, hg]
end Formalism.GM.FrozenVariableComponents
