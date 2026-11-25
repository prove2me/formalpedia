-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.re_mdisc_cons_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:19.374959+00:00
-- url     : https://prove2.me/submissions/a68fd72f-6bc7-46b4-852f-49bf09a7eaef

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_conjTranspose
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_vecMulVec_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (a b : Fin (n + 1) → ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).PosSemidef) :
    (mdisc (Fin.cons (vecMulVec a (star b)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re ^ 2 ≤
      (mdisc (Fin.cons (vecMulVec a (star a)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re *
      (mdisc (Fin.cons (vecMulVec b (star b)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
  set S : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ) → ℂ := fun x y =>
    mdisc (Fin.cons (vecMulVec x (star y)) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    with hS
  have hsym : (S b a).re = (S a b).re := by
    simp only [hS]
    rw [← re_mdisc_cons_conjTranspose _ B (fun i => (hB i).1), conjTranspose_vecMulVec, star_star]
  have hq : ∀ t : ℝ, 0 ≤ (S b b).re * (t * t) + (2 * (S a b).re) * t + (S a a).re := by
    intro t
    have h := re_mdisc_cons_vecMulVec_nonneg (a + (t : ℂ) • b) B hB
    have key : mdisc (Fin.cons (vecMulVec (a + (t : ℂ) • b) (star (a + (t : ℂ) • b))) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        S a a + (t : ℂ) * (S a b + S b a) + ((t * t : ℝ) : ℂ) * S b b := by
      simp only [hS, mdisc_cons_eq_sum, vecMulVec_apply, Finset.mul_sum, mul_add,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [key] at h
    simp only [Complex.add_re, Complex.re_ofReal_mul] at h
    rw [hsym] at h
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  simp only [hS] at hd
  nlinarith [hd]
end ReciprocityTheory.AnForm.A
