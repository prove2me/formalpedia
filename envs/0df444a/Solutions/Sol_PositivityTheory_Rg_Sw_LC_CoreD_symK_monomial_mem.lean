-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.symK_monomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:34.187119+00:00
-- url     : https://prove2.me/submissions/cebf132b-5fac-49ca-b4e3-6ea7c47321ec

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symK_X
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_monomial_mem_S
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_deg_add

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution {N : ℕ} (i j : Fin n) {t} (ht : t ∈ U ε N) (r : ℂ) :
    symK ε i j (monomial t r) ∈ S (n := n) ε N := by
  unfold symK
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v hv => ?_)
  dsimp only
  have hsymk := symK_X (ε := ε) i j v
  unfold symK at hsymk
  rw [mkDerivation_X] at hsymk
  rcases hsymk with h0 | ⟨v', c, hc, hv'⟩
  · rw [h0, smul_zero]; exact Submodule.zero_mem _
  · rw [hc, smul_eq_mul, mul_smul_comm, X, monomial_mul]
    refine Submodule.smul_mem _ _ (monomial_mem_S ⟨?_, ?_⟩ _)
    · have hle : Finsupp.single v 1 ≤ t := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
      have e1 := deg_add (t - Finsupp.single v 1) (Finsupp.single v 1)
      rw [tsub_add_cancel_of_le hle] at e1
      rw [deg_add]
      have : ((Finsupp.single v' 1 : _ →₀ ℕ).sum fun _ e => e) = ((Finsupp.single v 1 : _ →₀ ℕ).sum fun _ e => e) := by
        simp [Finsupp.sum_single_index]
      rw [this, ← e1]; exact ht.1
    · intro w hw
      rcases Finset.mem_union.1 (Finsupp.support_add hw) with hw | hw
      · exact ht.2 w (Finsupp.support_tsub hw)
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hw
        exact hw ▸ hv'
end PositivityTheory.Rg.Sw.LC.CoreD
