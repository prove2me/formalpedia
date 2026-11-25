-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:16:54.775714+00:00
-- url     : https://prove2.me/submissions/bb135dc2-063c-4773-b03d-6651a1299147

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
import Theorems.Thm_PI_CubicExponentialFactor_Wk_logMv_eq
import Theorems.Thm_PI_CubicExponentialFactor_Wk_expMv_eq
import Theorems.Thm_PI_CubicExponentialFactor_Wk_expMv_addC
import Theorems.Thm_P2M_PI_FglShared_expMv_subst__fa51dcff15ff
import Theorems.Thm_PI_CubicExponentialFactor_Wk_wq_int
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_mul
import Theorems.Thm_PI_FglShared_constantCoeff_logS
import Theorems.Thm_PI_FglShared_exists_coeff_ne
import Theorems.Thm_PI_FglShared_expMv_logS
import Theorems.Thm_PI_FglShared_l_constantCoeff
import Theorems.Thm_PI_FglShared_subst_ne_zero
import Theorems.Thm_PI_FglShared_subst_subst_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor MvPowerSeries PI.FglShared
set_option linter.unusedSimpArgs false
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution : Lemma := by
  intro p _ W wq l ex E T ha1 ha2 ha3 ha4 ha6 hW hex0 hinv hE0 hT ⟨n, hnI, hn1, hTn⟩
  classical

  set x0 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 0 with hx0
  set x1 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 1 with hx1
  set x2 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 2 with hx2
  have hl0 : PowerSeries.constantCoeff l = 0 := PI.FglShared.l_constantCoeff hex0 hinv
  have hL0 : MvPowerSeries.constantCoeff (logS E) = 0 := PI.FglShared.constantCoeff_logS E
  have hXc : ∀ i : Fin 3, constantCoeff (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    intro i
    simp [Xv]
  have hlg0 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (lg l a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hl0
  have hpt0 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (pt ex a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hex0
  have hadd0 : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      constantCoeff (add l ex a b) = 0 := by
    intro a b ha hb
    unfold add
    exact hpt0 _ (by rw [map_add, hlg0 a ha, hlg0 b hb, add_zero])
  have hsub0 : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      constantCoeff (sub l ex a b) = 0 := by
    intro a b ha hb
    unfold sub
    exact hpt0 _ (by rw [map_sub, hlg0 a ha, hlg0 b hb, sub_zero])
  have c0 : constantCoeff x0 = 0 := hXc 0
  have c1 : constantCoeff x1 = 0 := hXc 1
  have c2 : constantCoeff x2 = 0 := hXc 2
  set s := add l ex (add l ex x0 x1) x2 with hs
  set d1 := sub l ex x0 x1 with hd1
  set d2 := sub l ex x1 x2 with hd2
  set d3 := sub l ex x2 x0 with hd3
  have cs : constantCoeff s = 0 := hadd0 _ _ (hadd0 _ _ c0 c1) c2
  have cd1 : constantCoeff d1 = 0 := hsub0 _ _ c0 c1
  have cd2 : constantCoeff d2 = 0 := hsub0 _ _ c1 c2
  have cd3 : constantCoeff d3 = 0 := hsub0 _ _ c2 c0

  set ψ : MvPowerSeries (Fin 3) ℂ_[p] → MvPowerSeries (Fin 3) ℂ_[p] :=
    fun a => PowerSeries.subst a (logS E) with hψdef
  have hψ0 : ∀ a, constantCoeff a = 0 → constantCoeff (ψ a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hL0
  have hexpψ : ∀ a, constantCoeff a = 0 → expMv (ψ a) = eAt E a := by
    intro a ha
    rw [expMv_eq, PI.FglShared.expMv_subst' ha hL0, PI.FglShared.expMv_logS hE0]
    rfl
  have hφ : ∀ a, constantCoeff a = 0 → phAt E a = -ψ a := by
    intro a ha
    have hsa : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hsa, map_neg, PowerSeries.coe_substAlgHom hsa]

  set A := ψ s + ψ d1 + ψ d2 + ψ d3 with hA
  set B := ψ x0 + ψ x1 + ψ x2 with hB
  have cA : constantCoeff A = 0 := by
    simp only [hA, map_add, hψ0 _ cs, hψ0 _ cd1, hψ0 _ cd2, hψ0 _ cd3, add_zero]
  have cB : constantCoeff B = 0 := by
    simp only [hB, map_add, hψ0 _ c0, hψ0 _ c1, hψ0 _ c2, add_zero]
  have hFG : (phAt E s + phAt E d1 + phAt E d2 + phAt E d3) - 3 * (phAt E x0 + phAt E x1 + phAt E x2) =
      -A + (B + B + B) := by
    rw [hφ _ cs, hφ _ cd1, hφ _ cd2, hφ _ cd3, hφ _ c0, hφ _ c1, hφ _ c2]
    simp only [hA, hB]
    ring
  have cFG : constantCoeff (-A + (B + B + B)) = 0 := by
    simp only [map_add, map_neg, cA, cB, neg_zero, add_zero]
  set Z := expMv (-A + (B + B + B)) with hZdef
  have hexpA : expMv A = eAt E s * eAt E d1 * eAt E d2 * eAt E d3 := by
    have h1 : constantCoeff (ψ s + ψ d1) = 0 := by rw [map_add, hψ0 _ cs, hψ0 _ cd1, add_zero]
    have h2 : constantCoeff (ψ s + ψ d1 + ψ d2) = 0 := by rw [map_add, h1, hψ0 _ cd2, add_zero]
    rw [hA, expMv_addC h2 (hψ0 _ cd3), expMv_addC h1 (hψ0 _ cd2), expMv_addC (hψ0 _ cs) (hψ0 _ cd1),
      hexpψ _ cs, hexpψ _ cd1, hexpψ _ cd2, hexpψ _ cd3]
  have hexpB : expMv B = eAt E x0 * eAt E x1 * eAt E x2 := by
    have h1 : constantCoeff (ψ x0 + ψ x1) = 0 := by rw [map_add, hψ0 _ c0, hψ0 _ c1, add_zero]
    rw [hB, expMv_addC h1 (hψ0 _ c2), expMv_addC (hψ0 _ c0) (hψ0 _ c1), hexpψ _ c0, hexpψ _ c1,
      hexpψ _ c2]
  have hexp3B : expMv (B + B + B) = (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 := by
    have h1 : constantCoeff (B + B) = 0 := by rw [map_add, cB, add_zero]
    rw [expMv_addC h1 cB, expMv_addC cB cB, hexpB]
    ring
  have hZA : Z * (eAt E s * eAt E d1 * eAt E d2 * eAt E d3) = (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 := by
    rw [← hexpA, ← hexp3B, hZdef, ← expMv_addC cFG cA]
    congr 1
    ring

  obtain ⟨k, hk0, hkl⟩ := PI.FglShared.exists_coeff_ne hex0 hinv
  have hcoef : ∀ i j : Fin 3, MvPowerSeries.coeff (Finsupp.single i k)
      (lg l (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p])) = if i = j then PowerSeries.coeff k l else 0 := by
    intro i j
    unfold lg
    rw [PowerSeries.coeff_subst_single]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji, Finsupp.single_apply, hk0]
  have hne : ∀ (y : MvPowerSeries (Fin 3) ℂ_[p]) (i : Fin 3),
      MvPowerSeries.coeff (Finsupp.single i k) y = PowerSeries.coeff k l → y ≠ 0 := by
    intro y i hy h0
    rw [h0, map_zero] at hy
    exact hkl hy.symm
  have hlgadd : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      lg l (add l ex a b) = lg l a + lg l b := by
    intro a b ha hb
    have hy : constantCoeff (lg l a + lg l b) = 0 := by rw [map_add, hlg0 a ha, hlg0 b hb, add_zero]
    unfold add pt lg
    exact PI.FglShared.subst_subst_eq hex0 hinv hy
  have hptne : ∀ y : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff y = 0 → y ≠ 0 → pt ex y ≠ 0 := by
    intro y hy0 hy
    unfold pt
    exact PI.FglShared.subst_ne_zero hex0 hinv hy0 hy
  have e0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x0) = PowerSeries.coeff k l := by
    have h := hcoef 0 0
    rw [if_pos rfl] at h
    exact h
  have e1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x1) = 0 := by
    have h := hcoef 0 1
    rw [if_neg (by decide)] at h
    exact h
  have e2 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x2) = 0 := by
    have h := hcoef 0 2
    rw [if_neg (by decide)] at h
    exact h
  have f1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) k) (lg l x1) = PowerSeries.coeff k l := by
    have h := hcoef 1 1
    rw [if_pos rfl] at h
    exact h
  have f2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) k) (lg l x2) = 0 := by
    have h := hcoef 1 2
    rw [if_neg (by decide)] at h
    exact h
  have g2 : MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) k) (lg l x2) = PowerSeries.coeff k l := by
    have h := hcoef 2 2
    rw [if_pos rfl] at h
    exact h
  have g0 : MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) k) (lg l x0) = 0 := by
    have h := hcoef 2 0
    rw [if_neg (by decide)] at h
    exact h
  have hs0 : s ≠ 0 := by
    have hs' : s = pt ex (lg l x0 + lg l x1 + lg l x2) := by
      show pt ex (lg l (add l ex x0 x1) + lg l x2) = _
      rw [hlgadd x0 x1 c0 c1]
    rw [hs']
    refine hptne _ (by rw [map_add, map_add, hlg0 _ c0, hlg0 _ c1, hlg0 _ c2]; simp) (hne _ 0 ?_)
    rw [map_add, map_add, e0, e1, e2]
    simp
  have hd10 : d1 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c0, hlg0 _ c1, sub_zero]) (hne _ 0 ?_)
    rw [map_sub, e0, e1, sub_zero]
  have hd20 : d2 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c1, hlg0 _ c2, sub_zero]) (hne _ 1 ?_)
    rw [map_sub, f1, f2, sub_zero]
  have hd30 : d3 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c2, hlg0 _ c0, sub_zero]) (hne _ 2 ?_)
    rw [map_sub, g2, g0, sub_zero]
  have hE1 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (eAt E a) = 1 := by
    intro a ha
    have hsa := PowerSeries.HasSubst.of_constantCoeff_zero ha
    have h1 : constantCoeff (PowerSeries.subst a (E - 1)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha _ (by rw [map_sub, hE0, map_one, sub_self])
    rw [← PowerSeries.coe_substAlgHom hsa, map_sub, map_one, map_sub, map_one, sub_eq_zero] at h1
    unfold eAt
    rw [← PowerSeries.coe_substAlgHom hsa]
    exact h1
  have hR : (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_pow, map_mul, map_mul, hE1 _ c0, hE1 _ c1, hE1 _ c2, map_zero] at this
    norm_num at this

  have hT' : s * d1 * d2 * d3 * n * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 =
      (eAt wq x0 * eAt wq x1 * eAt wq x2) * (s * d1 * d2 * d3) *
        (eAt E s * eAt E d1 * eAt E d2 * eAt E d3) := by
    rw [hTn] at hT
    linear_combination hT
  have hkey : (s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3) * (n * Z) =
      (s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3) * (eAt wq x0 * eAt wq x1 * eAt wq x2) := by
    linear_combination Z * hT' + ((eAt wq x0 * eAt wq x1 * eAt wq x2) * (s * d1 * d2 * d3)) * hZA
  have hQR : s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hd10) hd20) hd30) hR
  have hnZ : n * Z = eAt wq x0 * eAt wq x1 * eAt wq x2 := mul_left_cancel₀ hQR hkey

  let Wr : Subring ℂ_[p] :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) =>
        show ‖a * b‖ ≤ 1 by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := show ‖(1 : ℂ_[p])‖ ≤ 1 by rw [norm_one]
      add_mem' := fun {a b} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) =>
        show ‖a + b‖ ≤ 1 from (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := show ‖(0 : ℂ_[p])‖ ≤ 1 by rw [norm_zero]; exact zero_le_one
      neg_mem' := fun {a} (ha : ‖a‖ ≤ 1) => show ‖-a‖ ≤ 1 by rw [norm_neg]; exact ha }
  let n' : MvPowerSeries (Fin 3) Wr := fun α => ⟨MvPowerSeries.coeff α n, hnI α⟩
  have hmap : MvPowerSeries.map Wr.subtype n' = n := by
    ext α
    rfl
  have hcn' : constantCoeff n' = 1 := by
    apply Subtype.ext
    have : Wr.subtype (constantCoeff n') = 1 := by
      rw [← MvPowerSeries.constantCoeff_map, hmap, hn1]
    exact this
  obtain ⟨u, hu⟩ : IsUnit n' := MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hcn']; exact isUnit_one)
  set v := MvPowerSeries.map Wr.subtype (↑u⁻¹ : MvPowerSeries (Fin 3) Wr) with hv
  have hnv : n * v = 1 := by
    rw [hv, ← hmap, ← hu, ← map_mul, Units.mul_inv, map_one]
  have hZP : Z = (eAt wq x0 * eAt wq x1 * eAt wq x2) * v := by
    calc Z = (n * v) * Z := by rw [hnv, one_mul]
      _ = (n * Z) * v := by ring
      _ = _ := by rw [hnZ]
  have hwqW : ∀ i : Fin 3, PI.FglPhSplit.Wk.AllIn Wr (eAt wq (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p])) := by
    intro i α
    unfold eAt
    rw [PowerSeries.coeff_subst_single]
    split_ifs
    · exact PI.CubicExponentialFactor.Wk.wq_int ha1 ha2 ha3 ha4 ha6 hW _
    · exact Wr.zero_mem
  have hvW : PI.FglPhSplit.Wk.AllIn Wr v := by
    intro α
    rw [hv, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff α (↑u⁻¹ : MvPowerSeries (Fin 3) Wr)).2
  have hZW : PI.FglPhSplit.Wk.AllIn Wr Z := by
    rw [hZP]
    exact PI.FglPhSplit.Wk.allIn_mul (PI.FglPhSplit.Wk.allIn_mul
      (PI.FglPhSplit.Wk.allIn_mul (hwqW 0) (hwqW 1)) (hwqW 2)) hvW
  unfold Simeq
  rw [hFG]
  exact ⟨cFG, fun α => hZW α⟩
end PI.CubicExponentialFactor.Wk
