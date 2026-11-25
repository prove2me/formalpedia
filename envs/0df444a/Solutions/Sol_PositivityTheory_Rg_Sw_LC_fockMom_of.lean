-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.fockMom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:45.738485+00:00
-- url     : https://prove2.me/submissions/6dcf04aa-6121-4bcc-85fd-642fabaa9bf7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMomOfBasic
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_fock_C
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_deg_lt
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_fock_X
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_C
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_flip_flip
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.flip_flip



set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
variable (hM : OneMom)
include hB hM
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : FockMom := by
  intro m n c hc
  obtain ⟨hL, -, -⟩ := hB m n c hc
  have h1 : mom c (1 : PX m n) ≠ 0 := by
    rw [← C_1, ← monomial_zero', mom_monomial hM c hc, one_mul, phi]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [Finsupp.coe_zero, Pi.zero_apply, g1, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
      pow_one, if_true]
    exact_mod_cast (div_pos Real.pi_pos hc).ne'
  refine ⟨h1, ?_⟩
  let D : PX m n → ℂ := fun p => mom c (fock c p) - mom c (1 : PX m n) * contr c p
  have hDadd : ∀ p q, D (p + q) = D p + D q := by
    intro p q; simp only [D]; rw [hL.map_add, mom_add hM c hc, contr_add]; ring
  have hDC : ∀ r, D (C r) = 0 := by
    intro r; simp only [D]
    rw [fock_C, contr_C, C_eq_smul_one, mom_smul]; ring
  have hDX : ∀ k p, D (X k * p) = (2 * c : ℂ) * D (pderiv (flip k) p) := by
    intro k p; simp only [D]; rw [mom_fock_X hB hM c hc, contr_X_mul]; ring
  have hmono : ∀ N, ∀ s : Fin m × Fin n × Bool →₀ ℕ, ∑ x, s x = N → ∀ r, D (monomial s r) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro s hs r
      by_cases h0 : s = 0
      · subst h0; rw [monomial_zero']; exact hDC r
      · obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
        have hk' : s k ≠ 0 := by simpa using hk
        have hs' : Finsupp.single k 1 + (s - Finsupp.single k 1) = s := by
          ext x
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hx
          · subst hx; omega
          · simp
        have hXm : monomial s r = (X k : PX m n) * monomial (s - Finsupp.single k 1) r := by
          rw [X, monomial_mul, one_mul, hs']
        rw [hXm, hDX, pderiv_monomial]
        have hlt : ∑ x, ((s - Finsupp.single k 1 - Finsupp.single (flip k) 1 : Fin m × Fin n × Bool →₀ ℕ) x) < N :=
          hs ▸ deg_lt s k hk' _ (fun x => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; exact tsub_le_self)
        rw [ih _ hlt _ rfl, mul_zero]
  intro p
  have hD0 : D p = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s r => exact hmono _ s rfl r
    | add p q hp hq => rw [hDadd, hp, hq, add_zero]
  exact sub_eq_zero.1 hD0
end PositivityTheory.Rg.Sw.LC
