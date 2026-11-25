-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyc_pcl_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:04.432393+00:00
-- url     : https://prove2.me/submissions/b647cb27-d486-49e6-9fbc-d58f0515afdf

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne
import Theorems.Thm_ReciprocityTheory_Cheb_cyc_psum_bdd
import Theorems.Thm_ReciprocityTheory_Cheb_tendsto_log_one_div_sub_one
import Theorems.Thm_ReciprocityTheory_Cheb_Smooth_mono
import Theorems.Thm_ReciprocityTheory_Cheb_pcl_one_le_re_psum_one
import Theorems.Thm_ReciprocityTheory_Cheb_psum_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (a : (ZMod l)ˣ) (X : ℝ) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), X ≤ Pcl E l (a : ZMod l) s := by
  have hB0 : ∀ χ : DirichletCharacter ℂ l, ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → ‖Psum E χ s‖ ≤ B := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
    · obtain ⟨B, hB⟩ := cyc_psum_bdd (E := E) h1 h2 h3a h3c hK hS1 hirr χ hχ
      exact ⟨B, hB.mono fun _ h _ => h⟩
  choose B hB using hB0
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  obtain ⟨HighestWeightIntegral, hC3b⟩ := h3b E
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ, χ ≠ 1 → ‖Psum E χ s‖ ≤ B χ := eventually_all.2 hB
  set k : ℝ := ((l - 1 : ℕ) : ℝ) with hk
  set S : ℝ := ∑ χ : DirichletCharacter ℂ l, |B χ| with hSdef
  have hkpos : 0 < k := by
    have := (Fact.out : l.Prime).two_le
    rw [hk]; exact_mod_cast (by omega : 0 < l - 1)
  have hbig := tendsto_log_one_div_sub_one.eventually (eventually_ge_atTop (k * (k * X + S) + HighestWeightIntegral + C1))
  filter_upwards [hall, hC1, hbig, Ioc_mem_nhdsGT one_lt_two] with s hs hs1 hlog hsI
  have hgt : 1 < s := hsI.1
  have hS := h1.2.2 E s hgt
  have htot : (Nat.totient l : ℝ) = k := by rw [hk, Nat.totient_prime Fact.out]
  have ho := psum_orth (E := E) l a s hS
  have hore : ∑ χ : DirichletCharacter ℂ l, (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re
      = k * Pcl E l (a : ZMod l) s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this, ← htot]; simp
  have hterm : ∀ χ : DirichletCharacter ℂ l,
      (if χ = 1 then (Psum E (1 : DirichletCharacter ℂ l) s).re else 0) - |B χ|
        ≤ (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re := by
    intro χ
    split_ifs with h
    · subst h
      rw [MulChar.one_apply_coe, one_mul]
      linarith [abs_nonneg (B 1)]
    · have h3 : ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s‖ ≤ B χ := by
        rw [norm_mul]
        calc ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l)‖ * ‖Psum E χ s‖ ≤ 1 * ‖Psum E χ s‖ :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          _ ≤ B χ := by rw [one_mul]; exact hs χ h
      have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h3)).1
      linarith [le_abs_self (B χ)]
  have hsum := Finset.sum_le_sum fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ l))) => hterm χ
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l), hore] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hp1 := pcl_one_le_re_psum_one (E := E) l s hS
  have hpe : Real.log (1 / (s - 1)) - HighestWeightIntegral ≤ PE E s := by
    have := hC3b s hsI
    linarith [(abs_le.mp this).1]

  have hk1 : k * (k * X + S) ≤ k * Pcl E l 1 s := by linarith
  have hk2 : k * X + S ≤ Pcl E l 1 s := le_of_mul_le_mul_left hk1 hkpos
  have hk3 : k * X ≤ k * Pcl E l (a : ZMod l) s := by linarith
  exact le_of_mul_le_mul_left hk3 hkpos
end ReciprocityTheory.Cheb
