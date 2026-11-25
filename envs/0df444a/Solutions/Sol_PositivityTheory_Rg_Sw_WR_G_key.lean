-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:05.104594+00:00
-- url     : https://prove2.me/submissions/213e99d7-e159-4859-ae87-16acc907a322

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_herm_isHermitian
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_sec_add
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_sec_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_sec_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_amat_inv_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_mm_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open GM
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (hI : IntegP) (hW : Wick) (hR : Rot) (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ P : PX m n, ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y := by

  let S : Submodule ℂ (PX m n) :=
    { carrier := {P | ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
        secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y}
      add_mem' := by
        rintro P Q ⟨R1, h1⟩ ⟨R2, h2⟩
        refine ⟨R1 + R2, fun y => ?_⟩
        rw [sec_add hI hc (herm_isHermitian y), h1, h2]
        simp [evUV, map_add]; ring
      zero_mem' := ⟨0, fun y => by simp [sec_zero, evUV]⟩
      smul_mem' := by
        rintro r P ⟨R1, h1⟩
        refine ⟨MvPolynomial.C r * R1, fun y => ?_⟩
        rw [sec_smul, h1]
        simp [evUV]; ring }
  have hmono : ∀ N : ℕ, ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, d.sum (fun _ e => e) = N → monomial d (1 : ℂ) ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro d hd
      by_cases ht : ∃ k : Fin m × Fin n × Bool, k.2.2 = true ∧ d k ≠ 0
      · obtain ⟨⟨a, i, bb⟩, hk, hdk⟩ := ht
        simp only at hk
        subst hk
        set k : Fin m × Fin n × Bool := (a, i, true) with hkdef
        set d' := d - Finsupp.single k 1 with hd'
        have hdd : d = Finsupp.single k 1 + d' := by
          rw [hd', add_comm, tsub_add_cancel_of_le]
          intro j
          by_cases hj : j = k
          · subst hj; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hj]
        have hsum' : d'.sum (fun _ e => e) + 1 = N := by
          rw [← hd, hdd, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
          simp [Finsupp.sum_single_index]; ring
        have hmul : monomial d (1 : ℂ) = X k * monomial d' 1 := by
          rw [hdd, X, monomial_mul, one_mul]

        have hder : ∀ j : Fin n, pderiv ((a, j, false) : Fin m × Fin n × Bool) (monomial d' (1 : ℂ)) ∈ S := by
          intro j
          rw [pderiv_monomial]
          by_cases h0 : d' (a, j, false) = 0
          · rw [h0]; simp
          · rw [show (monomial (d' - Finsupp.single (a, j, false) 1)) ((1 : ℂ) * ↑(d' (a, j, false))) =
                ((d' (a, j, false) : ℂ)) • monomial (d' - Finsupp.single (a, j, false) 1) (1 : ℂ) by
                rw [smul_monomial, smul_eq_mul, one_mul, mul_one]]
            refine S.smul_mem _ (ih _ ?_ _ rfl)
            have hle : Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 ≤ d' := by
              intro l; by_cases hl : l = (a, j, false)
              · subst hl; simp; omega
              · simp [Finsupp.single_apply, Ne.symm hl]
            have e2 : d' = Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 +
                (d' - Finsupp.single (a, j, false) 1) := by rw [add_comm, tsub_add_cancel_of_le hle]
            have : (d' - Finsupp.single (a, j, false) 1).sum (fun _ e => e) + 1 = d'.sum (fun _ e => e) := by
              conv_rhs => rw [e2]
              rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
              simp [Finsupp.sum_single_index]; ring
            omega
        choose R hR using hder
        refine ⟨∑ j, MvPolynomial.C ((c : ℂ)⁻¹) *
          MvPolynomial.X (if ε a then ((false, i, j) : Bool × Fin n × Fin n) else (true, i, j)) * R j, fun y => ?_⟩
        rw [hmul, hW m n ε c (s * c) hc _ (herm_isHermitian y)]
        simp_rw [hR]
        simp only [evUV, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [amat_inv_apply ε hc.ne' s (herm_isHermitian y), mm_inv]
        by_cases h : ε a = true <;> simp [h] <;> ring
      · push_neg at ht
        by_cases hd0 : d = 0
        · subst hd0
          exact ⟨1, fun y => by simp [evUV]⟩
        · refine ⟨0, fun y => ?_⟩
          rw [hR m n ε c (s * c) hc _ (herm_isHermitian y) d (fun k hk => ht k hk) hd0]
          simp [evUV]
  intro P
  have hP : P ∈ S := by
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one]]
    exact S.smul_mem _ (hmono _ d rfl)
  exact hP
end PositivityTheory.Rg.Sw.WR.G
