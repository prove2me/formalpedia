-- Prove2me | solution 1 for SWPort.Davenport.siegel_walfisz_ap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:43:21.940192+00:00
-- url     : https://prove2.me/submissions/81593c60-fedd-42b2-9d93-584a56da2a6e

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_psi_char_of_region
import Theorems.Thm_SWPort_Davenport_siegel_zero
import Theorems.Thm_SWPort_Davenport_zero_free_region

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel_walfisz_char
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel_walfisz_char` (361e2e5c-b3a6-4dd1-b105-c1910b0e314a, statement by alya); proof = accepted sketch submission 7ac4cba9-2179-4a59-8acd-ede7c1e8e684 by alya. -/

















open Finset DirichletCharacter Vino Davenport

namespace SWAux

/-- The denominator `log (q (|t| + 2))` of the zero-free region boundary is positive
whenever `q ≥ 1`. -/
private lemma log_region_pos (q : ℕ) (hq : 1 ≤ q) (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  refine Real.log_pos ?_
  have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith [abs_nonneg t]

/-- Shrinking the region constant shrinks the region. -/
private lemma inRegion_mono {q : ℕ} (hq : 1 ≤ q) {c c' : ℝ} (hc' : 0 < c') (hcc : c' ≤ c)
    {s : ℂ} (h : InRegion c' q s) : InRegion c q s := by
  have hL := log_region_pos q hq s.im
  have hd : c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    gcongr
  unfold InRegion regionBoundary at h ⊢
  linarith

/-- Trivial bound `‖ψ(N, χ)‖ ≤ N log N`. -/
private lemma norm_vmSumChar_le {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (hN : 1 ≤ N) :
    ‖vmSumChar q χ N‖ ≤ (N : ℝ) * Real.log N := by
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hstep : ∀ n ∈ Finset.range N,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤ Real.log N := by
    intro n hn
    have hle : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log N := by
      refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h, hlogN]
      · exact Real.log_le_log (by exact_mod_cast h)
          (by exact_mod_cast (Finset.mem_range.mp hn).le)
    have hnn : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
        = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod q)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _) hnn
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) := mul_one _
      _ ≤ Real.log N := hle
  calc ‖vmSumChar q χ N‖
      ≤ ∑ n ∈ Finset.range N, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, Real.log N := Finset.sum_le_sum hstep
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- For `L` beyond an explicit threshold, `A log L ≤ c₂ √L`. -/
private lemma log_le_sqrt_aux {A c₂ L : ℝ} (hA : 0 < A) (hc₂ : 0 < c₂)
    (h1 : 1 ≤ L) (h2 : (4 * A / c₂) ^ 4 ≤ L) : A * Real.log L ≤ c₂ * Real.sqrt L := by
  have hL0 : (0 : ℝ) < L := by linarith
  set v : ℝ := L ^ ((1 : ℝ) / 4) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hL0 _
  have hv4 : v ^ 4 = L := by
    rw [hvdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hL0.le]
    norm_num
  have hvge : 4 * A / c₂ ≤ v := by
    by_contra hcon
    push_neg at hcon
    have : v ^ 4 < (4 * A / c₂) ^ 4 := by
      exact pow_lt_pow_left₀ hcon hv0.le (by norm_num)
    rw [hv4] at this
    linarith
  have hsq : Real.sqrt L = v ^ 2 := by
    rw [← hv4, show v ^ 4 = (v ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hlogL : Real.log L = 4 * Real.log v := by
    rw [← hv4, Real.log_pow]; push_cast; ring
  have hlv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hv0
  rw [hsq, hlogL]
  have h4A : 4 * A ≤ c₂ * v := by
    have := (div_le_iff₀ hc₂).mp hvge
    nlinarith
  nlinarith [hv0, hlv, hA]

end SWAux

open SWAux in
open Classical in
theorem _root_.SWPort.Davenport.siegel_walfisz_char : ThreePrimes.SiegelWalfisz := by
  classical
  intro A hA
  -- Step 1: the classical zero-free region, with the constant shrunk so that every
  -- exceptional zero satisfies `β ≥ 1/2`.
  obtain ⟨c, hc, hzfr⟩ := Davenport.zero_free_region
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c₀ : ℝ := min c (Real.log 2 / 2) with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc (by linarith)
  have hc₀c : c₀ ≤ c := min_le_left _ _
  have hc₀half : c₀ ≤ Real.log 2 / 2 := min_le_right _ _
  -- Step 2: the explicit formula on that region.
  obtain ⟨c₁, c₂, Cp, hc₁, hc₂, hCp, hpsi⟩ := Davenport.psi_char_of_region c₀ hc₀pos
  -- Step 3: Siegel's theorem with `ε = 1/(2A)`.
  obtain ⟨CS, hCS, hsz⟩ := Davenport.siegel_zero (1 / (2 * A)) (by positivity)
  set ε : ℝ := 1 / (2 * A) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- Constants of the conclusion.
  set L₁ : ℝ := max 1 ((4 * A / c₂) ^ 4) with hL₁def
  have hL₁one : (1 : ℝ) ≤ L₁ := le_max_left _ _
  set cf : ℝ := min c₁ CS with hcfdef
  have hcfpos : 0 < cf := lt_min hc₁ hCS
  have hcfc₁ : cf ≤ c₁ := min_le_left _ _
  have hcfCS : cf ≤ CS := min_le_right _ _
  set Cf : ℝ := max (Cp + 2) ((L₁ + 1) * Real.exp (cf * Real.sqrt L₁)) with hCfdef
  refine ⟨Cf, cf, hcfpos, ?_⟩
  intro q hq χ N hN hqN
  haveI : NeZero q := ⟨by omega⟩
  set L : ℝ := Real.log N with hLdef
  have hNpos : (0 : ℕ) < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by exact_mod_cast hN)
  -- `q ≤ (log N)^A` and `q ≥ 1` force `log N ≥ 1`.
  have hL1 : 1 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have h1 : L ^ A < 1 := Real.rpow_lt_one hLpos.le hcon hA
    have h2 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith [hqN]
  have hexpL : Real.exp L = (N : ℝ) := by
    rw [hLdef, Real.exp_log hNR]
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  by_cases hcase : L₁ ≤ L
  · -- Main case.
    -- The hypothesis needed by `psi_char_of_region`.
    have hqexp : (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt L) := by
      have hkey : A * Real.log L ≤ c₂ * Real.sqrt L :=
        log_le_sqrt_aux hA hc₂ hL1 (le_trans (le_max_right _ _) hcase)
      have hrp : L ^ A = Real.exp (Real.log L * A) := Real.rpow_def_of_pos hLpos A
      have : L ^ A ≤ Real.exp (c₂ * Real.sqrt L) := by
        rw [hrp]
        exact Real.exp_le_exp.mpr (by linarith [hkey, mul_comm (Real.log L) A])
      exact le_trans hqN this
    -- The exceptional set for the shrunken constant.
    obtain ⟨E, hE, _hEd⟩ := hzfr q χ
    set E' : Set ℂ := {z | z ∈ E ∧ InRegion c₀ q z} with hE'def
    have hE'sub : E' ⊆ E := fun z hz => hz.1
    have hE' : IsExceptionalSet c₀ χ E' := by
      refine ⟨hE.1.anti hE'sub, ?_, ?_⟩
      · intro z hz
        obtain ⟨him, hre0, hre1, _, hz0, hqd, hne⟩ := hE.2.1 z hz.1
        exact ⟨him, hre0, hre1, hz.2, hz0, hqd, hne⟩
      · intro s hs1 hsreg hsE'
        refine hE.2.2 s hs1 (inRegion_mono hq hc₀pos hc₀c hsreg) ?_
        intro hsE
        exact hsE' ⟨hsE, hsreg⟩
    have hmain := hpsi q χ E' hE' N hN hqexp
    -- Bound the exceptional term.
    have hexc : ‖∑ᶠ z ∈ E', (N : ℂ) ^ z / z‖ ≤ 2 * (N : ℝ) * Real.exp (-CS * Real.sqrt L) := by
      rcases (hE.1.anti hE'sub).eq_empty_or_singleton with hemp | ⟨z₀, hsing⟩
      · rw [hemp, finsum_mem_empty, norm_zero]
        positivity
      · rw [hsing, finsum_mem_singleton]
        have hz₀ : z₀ ∈ E' := by rw [hsing]; exact rfl
        obtain ⟨him, hre0, hre1, hreg, hzero, hqd, hne⟩ := hE'.2.1 z₀ hz₀
        set β : ℝ := z₀.re with hβdef
        have hz₀eq : z₀ = (β : ℂ) := by
          apply Complex.ext <;> simp [hβdef, him]
        -- β ≥ 1/2 from the shrunken region.
        have hβhalf : (1 : ℝ) / 2 ≤ β := by
          have hlq : Real.log 2 ≤ Real.log ((q : ℝ) * (|z₀.im| + 2)) := by
            refine Real.log_le_log (by norm_num) ?_
            have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
            nlinarith [abs_nonneg z₀.im]
          have hpos := log_region_pos q hq z₀.im
          have : c₀ / Real.log ((q : ℝ) * (|z₀.im| + 2)) ≤ 1 / 2 := by
            rw [div_le_iff₀ hpos]
            calc c₀ ≤ Real.log 2 / 2 := hc₀half
              _ ≤ Real.log ((q : ℝ) * (|z₀.im| + 2)) / 2 := by linarith
              _ = 1 / 2 * Real.log ((q : ℝ) * (|z₀.im| + 2)) := by ring
          unfold InRegion regionBoundary at hreg
          rw [hβdef]
          linarith
        have hβpos : 0 < β := hre0
        -- Siegel: β ≤ 1 - CS q^{-ε}.
        have hcond_dvd : χ.conductor ∣ q := DirichletCharacter.conductor_dvd_level χ
        haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
        set χ' : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hχ'def
        have hchange : DirichletCharacter.changeLevel hcond_dvd χ' = χ :=
          χ.changeLevel_primitiveCharacter
        have hβne1 : ((β : ℂ)) ≠ 1 := by
          intro h
          have hb : β = 1 := by exact_mod_cast h
          linarith
        have hfac : DirichletCharacter.LFunction χ (β : ℂ) =
            DirichletCharacter.LFunction χ' (β : ℂ) *
              ∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-(β : ℂ))) := by
          conv_lhs => rw [← hchange]
          exact DirichletCharacter.LFunction_changeLevel hcond_dvd χ' (Or.inr hβne1)
        have hprodne : (∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-(β : ℂ)))) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro p hp
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
          have hppos : 0 < p := by omega
          intro hcontra
          have h1 : χ' p * (p : ℂ) ^ (-(β : ℂ)) = 1 := by
            have := sub_eq_zero.mp hcontra
            exact this.symm
          have h2 : ‖χ' (p : ZMod χ.conductor)‖ * ‖((p : ℂ)) ^ (-(β : ℂ))‖ = 1 := by
            rw [← norm_mul, h1, norm_one]
          have h3 : ‖((p : ℂ)) ^ (-(β : ℂ))‖ = (p : ℝ) ^ (-β) := by
            rw [Complex.norm_natCast_cpow_of_pos hppos]
            norm_num
          have h4 : (p : ℝ) ^ (-β) < 1 := by
            refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
            exact_mod_cast hp2
          have h5 : ‖χ' (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
          rw [h3] at h2
          nlinarith [norm_nonneg (χ' (p : ZMod χ.conductor)),
            Real.rpow_pos_of_pos (show (0:ℝ) < (p:ℝ) by exact_mod_cast hppos) (-β)]
        have hLχ' : DirichletCharacter.LFunction χ' (β : ℂ) = 0 := by
          rw [hz₀eq] at hzero
          rw [hfac] at hzero
          exact (mul_eq_zero.mp hzero).resolve_right hprodne
        have hχ'quad : χ'.IsQuadratic := by
          rw [MulChar.isQuadratic_iff_sq_eq_one]
          apply DirichletCharacter.changeLevel_injective (R := ℂ) hcond_dvd
          rw [map_pow, hchange, DirichletCharacter.changeLevel_one]
          exact hqd.sq_eq_one
        have hχ'ne1 : χ' ≠ 1 := by
          intro h
          apply hne
          rw [← hchange, h, DirichletCharacter.changeLevel_one]
        have hχ'prim : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
        have hsiegel := hsz χ.conductor χ' hχ'quad hχ'ne1 hχ'prim β
        have hβle : β ≤ 1 - CS * (χ.conductor : ℝ) ^ (-ε) := by
          by_contra hcon
          push_neg at hcon
          exact hsiegel hcon hLχ'
        -- Transfer to modulus `q` and then to `log N`.
        have hcondpos : 0 < χ.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
        have hcondle : (χ.conductor : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (by omega) hcond_dvd
        have hstep1 : (q : ℝ) ^ (-ε) ≤ (χ.conductor : ℝ) ^ (-ε) := by
          refine Real.rpow_le_rpow_of_nonpos ?_ hcondle (by linarith)
          exact_mod_cast hcondpos
        have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
        have hstep2 : (L ^ A) ^ (-ε) ≤ (q : ℝ) ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos hqRpos hqN (by linarith)
        have hstep3 : (L ^ A) ^ (-ε) = L ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ L)]
          congr 1
          rw [hεdef]
          field_simp
        have hstep4 : L ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt L := by
          rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ L), Real.sqrt_eq_rpow]
          simp
        have hβfin : β ≤ 1 - CS / Real.sqrt L := by
          have hchain : CS / Real.sqrt L ≤ CS * (χ.conductor : ℝ) ^ (-ε) := by
            have : (1 : ℝ) / Real.sqrt L ≤ (χ.conductor : ℝ) ^ (-ε) := by
              rw [← hstep4, ← hstep3]
              exact le_trans hstep2 hstep1
            calc CS / Real.sqrt L = CS * (1 / Real.sqrt L) := by ring
              _ ≤ CS * (χ.conductor : ℝ) ^ (-ε) := by
                  exact mul_le_mul_of_nonneg_left this hCS.le
          linarith
        -- `N^β ≤ N exp(-CS √log N)`.
        have hNβ : (N : ℝ) ^ β ≤ (N : ℝ) * Real.exp (-CS * Real.sqrt L) := by
          have hdef : (N : ℝ) ^ β = Real.exp (L * β) := by
            rw [Real.rpow_def_of_pos hNR, hLdef]
          have hle : L * β ≤ L - CS * Real.sqrt L := by
            have h1 : L * β ≤ L * (1 - CS / Real.sqrt L) := by
              exact mul_le_mul_of_nonneg_left hβfin (by linarith)
            have h2 : L * (1 - CS / Real.sqrt L) = L - CS * (L / Real.sqrt L) := by
              field_simp
            have h3 : L / Real.sqrt L = Real.sqrt L := Real.div_sqrt
            rw [h2, h3] at h1
            linarith
          rw [hdef]
          calc Real.exp (L * β) ≤ Real.exp (L - CS * Real.sqrt L) := Real.exp_le_exp.mpr hle
            _ = Real.exp L * Real.exp (-CS * Real.sqrt L) := by
                rw [← Real.exp_add]; ring_nf
            _ = (N : ℝ) * Real.exp (-CS * Real.sqrt L) := by rw [hexpL]
        -- Assemble.
        have hnormnum : ‖(N : ℂ) ^ z₀‖ = (N : ℝ) ^ β := by
          rw [Complex.norm_natCast_cpow_of_pos hNpos]
        have hnormden : ‖z₀‖ = β := by
          rw [hz₀eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβpos]
        rw [norm_div, hnormnum, hnormden]
        have hNβpos : (0 : ℝ) < (N : ℝ) ^ β := Real.rpow_pos_of_pos hNR β
        calc (N : ℝ) ^ β / β ≤ (N : ℝ) ^ β / (1 / 2) := by
              apply div_le_div_of_nonneg_left hNβpos.le (by norm_num) hβhalf
          _ = 2 * (N : ℝ) ^ β := by ring
          _ ≤ 2 * ((N : ℝ) * Real.exp (-CS * Real.sqrt L)) := by linarith
          _ = 2 * (N : ℝ) * Real.exp (-CS * Real.sqrt L) := by ring
    -- Combine the two bounds.
    have htri : ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖ ≤
        Cp * (N : ℝ) * Real.exp (-c₁ * Real.sqrt L) +
          2 * (N : ℝ) * Real.exp (-CS * Real.sqrt L) := by
      have := norm_sub_le (vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)
        + ∑ᶠ z ∈ E', (N : ℂ) ^ z / z) (∑ᶠ z ∈ E', (N : ℂ) ^ z / z)
      simp only [add_sub_cancel_right] at this
      linarith [hmain, hexc]
    have hcomp1 : Real.exp (-c₁ * Real.sqrt L) ≤ Real.exp (-cf * Real.sqrt L) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsqrtL.le]
    have hcomp2 : Real.exp (-CS * Real.sqrt L) ≤ Real.exp (-cf * Real.sqrt L) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsqrtL.le]
    have hCfge : Cp + 2 ≤ Cf := le_max_left _ _
    have hepos : 0 < Real.exp (-cf * Real.sqrt L) := Real.exp_pos _
    rw [show (Classical.propDecidable (χ = 1)) = FunLike.toDecidableEq χ 1 from Subsingleton.elim _ _]
    calc ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖
        ≤ Cp * (N : ℝ) * Real.exp (-c₁ * Real.sqrt L) +
            2 * (N : ℝ) * Real.exp (-CS * Real.sqrt L) := htri
      _ ≤ Cp * (N : ℝ) * Real.exp (-cf * Real.sqrt L) +
            2 * (N : ℝ) * Real.exp (-cf * Real.sqrt L) := by
          gcongr <;> positivity
      _ = (Cp + 2) * (N : ℝ) * Real.exp (-cf * Real.sqrt L) := by ring
      _ ≤ Cf * (N : ℝ) * Real.exp (-cf * Real.sqrt L) := by
          gcongr
  · -- Small `N`: the trivial bound suffices.
    push_neg at hcase
    have htriv : ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖ ≤ (N : ℝ) * (L₁ + 1) := by
      have h1 : ‖vmSumChar q χ N‖ ≤ (N : ℝ) * L := norm_vmSumChar_le χ N (by omega)
      have h2 : ‖(if χ = 1 then (N : ℂ) else 0)‖ ≤ (N : ℝ) := by
        split_ifs with h
        · simp
        · simp [hNR.le]
      have h4 := norm_sub_le (vmSumChar q χ N) (if χ = 1 then (N : ℂ) else 0)
      have h3 : (N : ℝ) * L ≤ (N : ℝ) * L₁ := mul_le_mul_of_nonneg_left hcase.le hNR.le
      linarith
    have hsq : Real.sqrt L ≤ Real.sqrt L₁ := Real.sqrt_le_sqrt hcase.le
    have hexpge : Real.exp (-cf * Real.sqrt L₁) ≤ Real.exp (-cf * Real.sqrt L) := by
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left hsq hcfpos.le]
    have hCfge : (L₁ + 1) * Real.exp (cf * Real.sqrt L₁) ≤ Cf := le_max_right _ _
    have hcancel : Real.exp (cf * Real.sqrt L₁) * Real.exp (-cf * Real.sqrt L₁) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [show (Classical.propDecidable (χ = 1)) = FunLike.toDecidableEq χ 1 from Subsingleton.elim _ _]
    calc ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖
        ≤ (N : ℝ) * (L₁ + 1) := htriv
      _ = ((L₁ + 1) * Real.exp (cf * Real.sqrt L₁)) * (N : ℝ) *
            Real.exp (-cf * Real.sqrt L₁) := by
          linear_combination (-((N : ℝ) * (L₁ + 1))) * hcancel
      _ ≤ Cf * (N : ℝ) * Real.exp (-cf * Real.sqrt L) := by
          gcongr <;> positivity

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel_walfisz_ap
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel_walfisz_ap` (ff9f3207-eba1-492e-9691-e50480292b68, statement by alya); proof = accepted sketch submission c971b7bd-d4d1-4c00-8af0-275aab368880 by alya. -/
/-
# Siegel–Walfisz in arithmetic progressions, from the character form

We derive `ψ(N; q, a) = N/φ(q) + O(N e^{-c√log N})` (uniformly for `q ≤ (log N)^A`,
`(a,q) = 1`) from the character form `‖ψ(N,χ) − δ_χ N‖ ≤ C N e^{-c√log N}` by finite
orthogonality of Dirichlet characters modulo `q`.
-/







open Finset

namespace SolSiegelWalfiszAP

/-- The number of Dirichlet characters mod `q` with values in `ℂ` is `φ(q)`. -/
private lemma card_char (q : ℕ) [NeZero q] :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) = (q.totient : ℝ) := by
  have h : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at h
  exact_mod_cast h

/-- **Orthogonality.**  For `a` a unit mod `q`,
`φ(q) · ψ(N; q, a) = ∑_{χ mod q} χ(a⁻¹) ψ(N, χ)`. -/
private lemma totient_mul_psiAP (N q a : ℕ) [NeZero q] (ha : IsUnit ((a : ZMod q))) :
    ((q.totient : ℂ)) * ((Davenport.psiAP N q a : ℝ) : ℂ)
      = ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * Vino.vmSumChar q χ N := by
  have h1 : ∀ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q))⁻¹ * Vino.vmSumChar q χ N
        = ∑ n ∈ range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (χ ((a : ZMod q))⁻¹ * χ ((n : ℕ) : ZMod q)) := by
    intro χ
    rw [Vino.vmSumChar, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl fun χ (_ : χ ∈ (univ : Finset (DirichletCharacter ℂ q))) => h1 χ,
    Finset.sum_comm, Davenport.psiAP, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha ((n : ℕ) : ZMod q)]
  by_cases h : ((n : ℕ) : ZMod q) = ((a : ℕ) : ZMod q)
  · rw [if_pos h, if_pos h.symm]
    ring
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    push_cast
    ring

-- The main terms collapse: only the principal character contributes, and it contributes `N`.
open Classical in
private lemma sum_char_main (N q a : ℕ) [NeZero q] (ha : IsUnit ((a : ZMod q))) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * (if χ = 1 then (N : ℂ) else 0)
      = (N : ℂ) := by
  have hinv : IsUnit (((a : ZMod q))⁻¹) :=
    IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit ((a : ZMod q)) ha)
  rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
  · rw [if_pos rfl, MulChar.one_apply hinv, one_mul]
  · intro χ _ hne
    rw [if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (1 : DirichletCharacter ℂ q)) h

end SolSiegelWalfiszAP

open Classical in
theorem _root_.SWPort.Davenport.siegel_walfisz_ap_oai (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N q a : ℕ), 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ A → Nat.Coprime a q →
        |Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)|
          ≤ C * N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨C, c, hc, hb⟩ := Davenport.siegel_walfisz_char A hA
  refine ⟨c, max C 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro N q a hN hq hqN hcop
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : 0 < q := hq
  have ha : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr hcop
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hφC : ((q.totient : ℂ)) ≠ 0 := by
    simpa using hφ.ne'
  set B : ℝ := C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) with hBdef
  -- The character-form bound, one character at a time.
  have hb' := fun (χ : DirichletCharacter ℂ q) => hb q hq χ N hN hqN
  -- The orthogonality identity.
  have key : ((q.totient : ℂ)) *
        (((Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ) : ℝ)) : ℂ)
      = ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q))⁻¹ * (Vino.vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)) := by
    have hsplit : (∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q))⁻¹ * (Vino.vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)))
        = (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * Vino.vmSumChar q χ N)
          - ∑ χ : DirichletCharacter ℂ q,
              χ ((a : ZMod q))⁻¹ * (if χ = 1 then (N : ℂ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [hsplit, ← SolSiegelWalfiszAP.totient_mul_psiAP N q a ha,
      SolSiegelWalfiszAP.sum_char_main N q a ha]
    push_cast
    field_simp
  -- Bound the character sum.
  have hsum : ‖∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q))⁻¹ * (Vino.vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0))‖
      ≤ (q.totient : ℝ) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : DirichletCharacter ℂ q => B) ?_) ?_
    · intro χ _
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_right
        (DirichletCharacter.norm_le_one χ (((a : ZMod q))⁻¹)) (norm_nonneg _)) ?_
      rw [one_mul]
      rw [show (FunLike.toDecidableEq χ 1) = Classical.propDecidable (χ = 1) from Subsingleton.elim _ _]; exact hb' χ
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        SolSiegelWalfiszAP.card_char q]
  -- Put the two together.
  have hnorm : (q.totient : ℝ) *
      |Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)| ≤ (q.totient : ℝ) * B := by
    have h1 : ‖((q.totient : ℂ)) *
        (((Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ) : ℝ)) : ℂ)‖
        ≤ (q.totient : ℝ) * B := by rw [key]; exact hsum
    rwa [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at h1
  have hfinal : |Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)| ≤ B :=
    le_of_mul_le_mul_left hnorm hφ
  refine hfinal.trans ?_
  rw [hBdef]
  have hexp : 0 < Real.exp (-c * Real.sqrt (Real.log N)) := Real.exp_pos _
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have : C * (N : ℝ) ≤ max C 1 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left C 1) hNn
  exact mul_le_mul_of_nonneg_right this hexp.le

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.siegel_walfisz_ap_oai := @SWPort.Davenport.siegel_walfisz_ap_oai
