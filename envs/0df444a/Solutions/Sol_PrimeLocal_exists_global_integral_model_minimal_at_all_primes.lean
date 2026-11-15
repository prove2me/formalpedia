-- Prove2me | solution 1 for PrimeLocal.exists_global_integral_model_minimal_at_all_primes
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:46.458189+00:00
-- url     : https://prove2.me/submissions/2918da96-acea-4695-b51b-bdccd381e899

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_isIntegralModelOf_rat
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
namespace PrimeLocal
/-- A rational elliptic curve admits an integral equation minimal at every prime.
Choose least absolute discriminant and descend any local improvement by approximation. -/
theorem _root_.solution (E : WeierstrassCurve ℚ) [E.IsElliptic] : ∃ (W : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ), C • E = W.map (Int.castRingHom ℚ) ∧ W.Δ ≠ 0 ∧ ∀ (q : ℕ) [Fact q.Prime], WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) := by
  classical
  have happrox (q : ℕ) [hq : Fact q.Prime] (W : WeierstrassCurve ℤ)
      (C : VariableChange ℚ_[q])
      (hCI : WeierstrassCurve.IsIntegral ℤ_[q] (C • W.map (Int.castRingHom ℚ_[q])))
      (k : ℤ) (hnorm : ‖(q : ℚ_[q]) ^ k‖ = ‖(C.u : ℚ_[q])‖) :
      ∃ (W' : WeierstrassCurve ℤ) (D : VariableChange ℚ),
        D • W.map (Int.castRingHom ℚ) = W'.map (Int.castRingHom ℚ) ∧
        (D.u : ℚ) = (q : ℚ) ^ k := by
    classical
    have hdense : DenseRange
        (fun a : Subring.closure ({(q : ℚ)⁻¹} : Set ℚ) => (a.val : ℚ_[q])) := by
      have hdense (x : ℚ_[q]) {ε : ℝ} (hε : 0 < ε) :
          ∃ (k : ℤ) (z : ℤ), ‖x - (z : ℚ_[q]) / (q : ℚ_[q]) ^ k‖ < ε := by
        by_cases hx : x = 0
        · exact ⟨0, 0, by simpa [hx] using hε⟩
        have hq0 : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast hq.out.ne_zero
        have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
        let k : ℤ := -x.valuation
        let a : ℚ_[q] := (q : ℚ_[q]) ^ k
        have ha : a ≠ 0 := zpow_ne_zero _ hq0
        have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
        have hnorm : ‖a * x‖ = 1 := by
          rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx]
          change (q : ℝ) ^ (-(-x.valuation)) * (q : ℝ) ^ (-x.valuation) = 1
          rw [neg_neg, ← zpow_add₀ hqr, add_neg_cancel, zpow_zero]
        let y : ℤ_[q] := ⟨a * x, hnorm.le⟩
        obtain ⟨z, hz⟩ := PadicInt.denseRange_intCast.exists_dist_lt y (mul_pos hε ha_pos)
        refine ⟨k, z, ?_⟩
        have hz' : ‖a * x - (z : ℚ_[q])‖ < ε * ‖a‖ := by
          simpa only [dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_intCast] using hz
        have heq : x - (z : ℚ_[q]) / a = (a * x - z) / a := by field_simp
        change ‖x - (z : ℚ_[q]) / a‖ < ε
        rw [heq, norm_div]
        exact (div_lt_iff₀ ha_pos).mpr hz'
    
      let S : Subring ℚ := Subring.closure ({(q : ℚ)⁻¹} : Set ℚ)
      have hpow (k : ℤ) : (q : ℚ) ^ k ∈ S := by
        cases k with
        | ofNat n =>
          change (q : ℚ) ^ n ∈ S
          exact S.pow_mem (natCast_mem S q) n
        | negSucc n =>
          simpa only [zpow_negSucc, inv_pow] using
            S.pow_mem (Subring.subset_closure (Set.mem_singleton _)) (n + 1)
      intro x
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨k, z, hz⟩ := hdense x hε
      have hmem : (z : ℚ) / (q : ℚ) ^ k ∈ S := by
        rw [div_eq_mul_inv, ← zpow_neg]
        exact S.mul_mem (intCast_mem S z) (hpow (-k))
      refine ⟨(((z : ℚ) / (q : ℚ) ^ k : ℚ) : ℚ_[q]), ⟨⟨_, hmem⟩, rfl⟩, ?_⟩
      simpa only [dist_eq_norm, Rat.cast_div, Rat.cast_intCast, Rat.cast_zpow,
        Rat.cast_natCast] using hz
  
    let S : Subring ℚ := Subring.closure ({(q : ℚ)⁻¹} : Set ℚ)
    have hden (a : ℚ) (ha : a ∈ S) : ∃ n : ℕ, a.den ∣ q ^ n := by
      induction ha using Subring.closure_induction with
      | mem x hx =>
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact ⟨1, by simp [Rat.den_inv, hq.out.ne_zero]⟩
      | zero => exact ⟨0, by simp⟩
      | one => exact ⟨0, by simp⟩
      | add x y hx hy hdx hdy =>
        obtain ⟨n, hn⟩ := hdx
        obtain ⟨m, hm⟩ := hdy
        exact ⟨n + m, (Rat.add_den_dvd x y).trans (by simpa [pow_add] using Nat.mul_dvd_mul hn hm)⟩
      | neg x hx hdx => simpa using hdx
      | mul x y hx hy hdx hdy =>
        obtain ⟨n, hn⟩ := hdx
        obtain ⟨m, hm⟩ := hdy
        exact ⟨n + m, (Rat.mul_den_dvd x y).trans (by simpa [pow_add] using Nat.mul_dvd_mul hn hm)⟩
  
    have hint (a : ℚ) (hden : ∃ n : ℕ, a.den ∣ q ^ n)
        (hint : ‖(a : ℚ_[q])‖ ≤ 1) : ∃ z : ℤ, (z : ℚ) = a := by
      have hnot : ¬ q ∣ a.den := by
        intro hd
        have hn := PadicInt.isUnit_iff.mp (PadicInt.isUnit_den a hint)
        have hlt := (PadicInt.norm_natCast_lt_one_iff (p := q)).mpr hd
        rw [hn] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨n, hn⟩ := hden
      have hcop : Nat.Coprime a.den (q ^ n) := hq.out.coprime_pow_of_not_dvd hnot
      have hden1 : a.den = 1 := (Nat.gcd_eq_left hn).symm.trans hcop.gcd_eq_one
      exact ⟨a.num, Rat.coe_int_num_of_den_eq_one hden1⟩
  
    have happ (F : (Fin 3 → ℚ_[q]) → (Fin 5 → ℚ_[q])) (hF : Continuous F)
        (x : Fin 3 → ℚ_[q]) (hint : ∀ i, ‖F x i‖ ≤ 1) :
        ∃ y : Fin 3 → S, ∀ i, ‖F (fun j => ((y j).val : ℚ_[q])) i‖ ≤ 1 := by
      have hball : IsOpen {a : ℚ_[q] | ‖a‖ ≤ 1} := by
        simpa only [Subtype.range_coe_subtype] using
          (PadicInt.isOpenEmbedding_coe (p := q)).isOpen_range
      have hU : IsOpen {y : Fin 3 → ℚ_[q] | ∀ i, ‖F y i‖ ≤ 1} := by
        have hopen := isOpen_iInter_of_finite fun i : Fin 5 =>
          hball.preimage ((continuous_apply i).comp hF)
        convert hopen using 1
        ext y
        simp
      have hD : DenseRange (fun y : Fin 3 → S => fun i => ((y i).val : ℚ_[q])) :=
        DenseRange.piMap (fun _ => hdense)
      exact hD.exists_mem_open hU ⟨x, hint⟩
  
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have hpow (n : ℤ) : (q : ℚ) ^ n ∈ S := by
      cases n with
      | ofNat n =>
        change (q : ℚ) ^ n ∈ S
        exact S.pow_mem (natCast_mem S q) n
      | negSucc n =>
        simpa only [zpow_negSucc, inv_pow] using
          S.pow_mem (Subring.subset_closure (Set.mem_singleton _)) (n + 1)
    let u : ℚ_[q] := ((q : ℚ_[q]) ^ k)⁻¹
    let V := W.map (Int.castRingHom ℚ_[q])
    let F : (Fin 3 → ℚ_[q]) → (Fin 5 → ℚ_[q]) := fun x =>
      ![u * (V.a₁ + 2 * x 1),
        u ^ 2 * (V.a₂ - x 1 * V.a₁ + 3 * x 0 - x 1 ^ 2),
        u ^ 3 * (V.a₃ + x 0 * V.a₁ + 2 * x 2),
        u ^ 4 * (V.a₄ - x 1 * V.a₃ + 2 * x 0 * V.a₂ - (x 2 + x 0 * x 1) * V.a₁ +
          3 * x 0 ^ 2 - 2 * x 1 * x 2),
        u ^ 6 * (V.a₆ + x 0 * V.a₄ + x 0 ^ 2 * V.a₂ + x 0 ^ 3 - x 2 * V.a₃ -
          x 2 ^ 2 - x 0 * x 2 * V.a₁)]
    have hF : Continuous F := by
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp [F] <;> fun_prop
    obtain ⟨WC, hWC⟩ := hCI.integral
    have hCnorm : ∀ i : Fin 5,
        ‖![(C • V).a₁, (C • V).a₂, (C • V).a₃, (C • V).a₄, (C • V).a₆] i‖ ≤ 1 := by
      intro i
      change ‖![(C • W.map (Int.castRingHom ℚ_[q])).a₁,
        (C • W.map (Int.castRingHom ℚ_[q])).a₂,
        (C • W.map (Int.castRingHom ℚ_[q])).a₃,
        (C • W.map (Int.castRingHom ℚ_[q])).a₄,
        (C • W.map (Int.castRingHom ℚ_[q])).a₆] i‖ ≤ 1
      rw [hWC]
      fin_cases i
      · exact WC.a₁.property
      · exact WC.a₂.property
      · exact WC.a₃.property
      · exact WC.a₄.property
      · exact WC.a₆.property
    have hunorm : ‖u‖ = ‖(C.u : ℚ_[q])⁻¹‖ := by
      change ‖((q : ℚ_[q]) ^ k)⁻¹‖ = _
      rw [norm_inv, norm_inv, hnorm]
    have hFnorm : ∀ i, ‖F ![C.r, C.s, C.t] i‖ ≤ 1 := by
      intro i
      have hi := hCnorm i
      fin_cases i <;>
        simpa [F, variableChange_def, norm_mul, norm_pow, hunorm] using hi
    obtain ⟨y, hy⟩ := happ F hF ![C.r, C.s, C.t] hFnorm
    let uS : Sˣ := {
      val := ⟨(q : ℚ) ^ k, hpow k⟩
      inv := ⟨(q : ℚ) ^ (-k), hpow (-k)⟩
      val_inv := by
        apply Subtype.ext
        change (q : ℚ) ^ k * (q : ℚ) ^ (-k) = 1
        simpa only [zpow_neg] using mul_inv_cancel₀ (zpow_ne_zero k hq0)
      inv_val := by
        apply Subtype.ext
        change (q : ℚ) ^ (-k) * (q : ℚ) ^ k = 1
        simpa only [zpow_neg] using inv_mul_cancel₀ (zpow_ne_zero k hq0) }
    let CS : VariableChange S := ⟨uS, y 0, y 1, y 2⟩
    let WS : WeierstrassCurve S := CS • W.map (Int.castRingHom S)
    let D : VariableChange ℚ := CS.map S.subtype
    have hmap : D • W.map (Int.castRingHom ℚ) = WS.map S.subtype := by
      have hbase : (W.map (Int.castRingHom S)).map S.subtype = W.map (Int.castRingHom ℚ) := by
        ext <;> simp
      simpa only [hbase] using (W.map (Int.castRingHom S)).map_variableChange CS S.subtype
    have htwo : ((2 : S).val : ℚ) = 2 := rfl
    have hthree : ((3 : S).val : ℚ) = 3 := rfl
    have hWSnorm : ∀ i : Fin 5,
        ‖((![WS.a₁.val, WS.a₂.val, WS.a₃.val, WS.a₄.val, WS.a₆.val] i : ℚ) : ℚ_[q])‖ ≤ 1 := by
      intro i
      have hi := hy i
      fin_cases i <;>
        simpa [F, WS, CS, uS, u, V, variableChange_def, ← zpow_neg, htwo, hthree] using hi
    obtain ⟨z₁, hz₁⟩ := hint WS.a₁.val (hden _ WS.a₁.property) (hWSnorm 0)
    obtain ⟨z₂, hz₂⟩ := hint WS.a₂.val (hden _ WS.a₂.property) (hWSnorm 1)
    obtain ⟨z₃, hz₃⟩ := hint WS.a₃.val (hden _ WS.a₃.property) (hWSnorm 2)
    obtain ⟨z₄, hz₄⟩ := hint WS.a₄.val (hden _ WS.a₄.property) (hWSnorm 3)
    obtain ⟨z₆, hz₆⟩ := hint WS.a₆.val (hden _ WS.a₆.property) (hWSnorm 4)
    refine ⟨⟨z₁, z₂, z₃, z₄, z₆⟩, D, ?_, rfl⟩
    rw [hmap]
    ext
    · exact hz₁.symm
    · exact hz₂.symm
    · exact hz₃.symm
    · exact hz₄.symm
    · exact hz₆.symm

  have hpositive (q : ℕ) [hq : Fact q.Prime] (W : WeierstrassCurve ℚ_[q])
      (C : VariableChange ℚ_[q])
      (hstrict : ((IsDiscreteValuationRing.maximalIdeal ℤ_[q]).valuation ℚ_[q]) W.Δ <
        ((IsDiscreteValuationRing.maximalIdeal ℤ_[q]).valuation ℚ_[q]) (C • W).Δ) :
      0 < (C.u : ℚ_[q]).valuation := by
    let v := (maximalIdeal ℤ_[q]).valuation ℚ_[q]
    have hu : v (C.u : ℚ_[q]) < 1 := by
      by_contra h
      have hule : 1 ≤ v (C.u : ℚ_[q]) := le_of_not_gt h
      have hu0 : v (C.u : ℚ_[q]) ≠ 0 := by simp
      have hinvle : (v (C.u : ℚ_[q]))⁻¹ ≤ 1 := (inv_le_one₀ (pos_iff_ne_zero.mpr hu0)).mpr hule
      have hp : ((v (C.u : ℚ_[q]))⁻¹) ^ 12 ≤ 1 := pow_le_one₀ zero_le hinvle
      have hΔle : v (C • W).Δ ≤ v W.Δ := by
        rw [variableChange_Δ, map_mul, map_pow]
        simpa using mul_le_of_le_one_left (show 0 ≤ v W.Δ from zero_le) hp
      exact not_le_of_gt hstrict hΔle
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
    have hmem : a ∈ IsLocalRing.maximalIdeal ℤ_[q] := by
      apply (valuation_lt_one_iff_mem (K := ℚ_[q]) (maximalIdeal ℤ_[q]) a).mp
      simpa only [ha] using hu
    have hnot : ¬ IsUnit a := by simpa [IsLocalRing.mem_maximalIdeal, nonunits] using hmem
    have hnorm : ‖(C.u : ℚ_[q])‖ < 1 := by
      rw [← ha]
      exact PadicInt.not_isUnit_iff.mp hnot
    rw [Padic.norm_eq_zpow_neg_valuation (Units.ne_zero C.u)] at hnorm
    have hp1 : 1 < (q : ℝ) := by exact_mod_cast hq.out.one_lt
    have hn := (zpow_lt_zpow_iff_right₀ hp1).mp (show (q : ℝ) ^ (-(C.u : ℚ_[q]).valuation) < (q : ℝ)^ (0 : ℤ) by simpa using hnorm)
    omega

  have hdecrease (q : ℕ) [hq : Fact q.Prime] (W W' : WeierstrassCurve ℤ)
      (D : VariableChange ℚ)
      (hD : D • W.map (Int.castRingHom ℚ) = W'.map (Int.castRingHom ℚ))
      (n : ℕ) (hn : 0 < n) (hu : (D.u : ℚ) = (q : ℚ)^n) (hΔ : W.Δ ≠ 0) :
      W'.Δ.natAbs < W.Δ.natAbs := by
    have hΔrat := congrArg WeierstrassCurve.Δ hD
    simp only [variableChange_Δ, map_Δ, Units.val_inv_eq_inv_val, hu] at hΔrat
    change ((q : ℚ)^n)⁻¹ ^ 12 * (W.Δ : ℚ) = (W'.Δ : ℚ) at hΔrat
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have hrelQ : (W.Δ : ℚ) = (q^n : ℚ)^12 * W'.Δ := by
      rw [← hΔrat]
      field_simp [hq0]
    have hrel : W.Δ = (q^n : ℤ)^12 * W'.Δ := by exact_mod_cast hrelQ
    have hΔ' : W'.Δ ≠ 0 := by intro h; simp [h] at hrel; exact hΔ hrel
    have hrelabs := congrArg Int.natAbs hrel
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hrelabs
    have hbig : 1 < (q^n)^12 := one_lt_pow₀ (one_lt_pow₀ hq.out.one_lt hn.ne') (by norm_num)
    rw [hrelabs]
    exact lt_mul_left (Int.natAbs_pos.mpr hΔ') hbig

  have hex : ∃ n : ℕ, ∃ (W : WeierstrassCurve ℤ)
      (C : VariableChange ℚ),
      C • E = W.map (Int.castRingHom ℚ) ∧ W.Δ.natAbs = n := by
    obtain ⟨W, C, hC⟩ := WeierstrassCurve.exists_isIntegralModelOf_rat E
    exact ⟨W.Δ.natAbs, W, C, hC, rfl⟩
  obtain ⟨W, C, hC, hn⟩ := Nat.find_spec hex
  have hmin (W' : WeierstrassCurve ℤ) (C' : VariableChange ℚ)
      (hC' : C' • E = W'.map (Int.castRingHom ℚ)) : W.Δ.natAbs ≤ W'.Δ.natAbs := by
    rw [hn]
    exact Nat.find_min' hex ⟨W', C', hC', rfl⟩
  have hΔQ : (W.Δ : ℚ) ≠ 0 := by
    have hunit := (WeierstrassCurve.isElliptic_iff (C • E)).mp inferInstance
    rw [hC, map_Δ] at hunit
    exact hunit.ne_zero
  have hΔ : W.Δ ≠ 0 := by exact_mod_cast hΔQ
  refine ⟨W, C, hC, hΔ, ?_⟩
  intro q hq
  by_contra hminlocal
  have hI : WeierstrassCurve.IsIntegral ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) := by
    refine ⟨W.map (Int.castRingHom ℤ_[q]), ?_⟩
    ext <;> simp [WeierstrassCurve.baseChange]
  have hwitness : ∃ Cq : VariableChange ℚ_[q],
      WeierstrassCurve.IsIntegral ℤ_[q] (Cq • W.map (Int.castRingHom ℚ_[q])) ∧
      valuation_Δ_aux ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) <
        valuation_Δ_aux ℤ_[q] (Cq • W.map (Int.castRingHom ℚ_[q])) := by
    by_contra h
    apply hminlocal
    constructor
    constructor
    · simpa only [one_smul] using hI
    · intro Cq hCq hle
      have hnot : ¬ valuation_Δ_aux ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) <
          valuation_Δ_aux ℤ_[q] (Cq • W.map (Int.castRingHom ℚ_[q])) :=
        fun hlt => h ⟨Cq, hCq, hlt⟩
      simpa only [one_smul] using le_of_not_gt hnot
  obtain ⟨Cq, hCq, hlt⟩ := hwitness
  let := hI
  let := hCq
  have hlt' :
      ((IsDiscreteValuationRing.maximalIdeal ℤ_[q]).valuation ℚ_[q])
          (W.map (Int.castRingHom ℚ_[q])).Δ <
        ((IsDiscreteValuationRing.maximalIdeal ℤ_[q]).valuation ℚ_[q])
          (Cq • W.map (Int.castRingHom ℚ_[q])).Δ := by
    change (valuation_Δ_aux ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) : WithZero (Multiplicative ℤ)) <
      (valuation_Δ_aux ℤ_[q] (Cq • W.map (Int.castRingHom ℚ_[q])) : WithZero (Multiplicative ℤ)) at hlt
    simpa only [valuation_Δ_aux_eq_of_isIntegral] using hlt
  have hk := hpositive q (W.map (Int.castRingHom ℚ_[q])) Cq hlt'
  have hnorm : ‖(q : ℚ_[q]) ^ (Cq.u : ℚ_[q]).valuation‖ = ‖(Cq.u : ℚ_[q])‖ := by
    rw [Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation (Units.ne_zero Cq.u)]
  obtain ⟨W', D, hD, huD⟩ := happrox q W Cq hCq (Cq.u : ℚ_[q]).valuation hnorm
  let n : ℕ := (Cq.u : ℚ_[q]).valuation.toNat
  have hnpos : 0 < n := by omega
  have hnu : (n : ℤ) = (Cq.u : ℚ_[q]).valuation := Int.toNat_of_nonneg hk.le
  have huD' : (D.u : ℚ) = (q : ℚ)^n := by
    rw [huD, ← hnu, zpow_natCast]
  have hsmall := hdecrease q W W' D hD n hnpos huD' hΔ
  have hnew : (D * C) • E = W'.map (Int.castRingHom ℚ) := by
    rw [mul_smul, hC, hD]
  exact not_lt_of_ge (hmin W' (D * C) hnew) hsmall

end PrimeLocal
