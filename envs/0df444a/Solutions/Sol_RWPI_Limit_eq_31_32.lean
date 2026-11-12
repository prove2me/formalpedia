-- Prove2me | solution 1 for RWPI.Limit.eq_31_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:23:04.631199+00:00
-- url     : https://prove2.me/submissions/3621902d-1921-4ace-b611-6756c1d6ad7a

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_RWPI_Limit_dualRep
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Theorems.Thm_RWPI_Limit_proposition_3

set_option autoImplicit false

open MeasureTheory RWPI.Limit WassersteinDRO.Regularization
open scoped ENNReal

namespace SolRWPILimitEq3132

private lemma ereal_add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ := by
  cases x <;> cases y <;> simp_all

private lemma finset_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ereal_add_ne_bot (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma finset_sum_coe_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

private lemma ereal_mul_iSup_of_pos {ι : Type*} [Nonempty ι] {c : ℝ} (hc : 0 < c)
    (f : ι → EReal) :
    ((c : ℝ) : EReal) * (⨆ x, f x) = ⨆ x, ((c : ℝ) : EReal) * f x := by
  apply le_antisymm
  · set M : EReal := ⨆ x, ((c : ℝ) : EReal) * f x
    cases hM : M with
    | top => exact le_top
    | bot =>
      have hall : ∀ x, f x = ⊥ := by
        intro x
        have hx : ((c : ℝ) : EReal) * f x ≤ ⊥ := hM ▸ le_iSup (fun y => ((c : ℝ) : EReal) * f y) x
        have hxeq : ((c : ℝ) : EReal) * f x = ⊥ := le_bot_iff.mp hx
        cases hfx : f x with
        | bot => rfl
        | coe r =>
          rw [hfx, ← EReal.coe_mul] at hxeq
          exact absurd hxeq (EReal.coe_ne_bot _)
        | top =>
          rw [hfx, EReal.coe_mul_top_of_pos hc] at hxeq
          exact absurd hxeq top_ne_bot
      have hsup : (⨆ x, f x) = ⊥ := iSup_eq_bot.mpr hall
      rw [hsup, EReal.coe_mul_bot_of_pos hc]
    | coe m₀ =>
      have hall : ∀ x, f x ≤ ((m₀ / c : ℝ) : EReal) := by
        intro x
        have hx : ((c : ℝ) : EReal) * f x ≤ ((m₀ : ℝ) : EReal) :=
          hM ▸ le_iSup (fun y => ((c : ℝ) : EReal) * f y) x
        cases hfx : f x with
        | bot => exact bot_le
        | coe r =>
          rw [hfx, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hx
          exact EReal.coe_le_coe_iff.mpr ((le_div_iff₀' hc).mpr hx)
        | top =>
          rw [hfx, EReal.coe_mul_top_of_pos hc] at hx
          exact absurd (top_le_iff.mp hx) (EReal.coe_ne_top _)
      have hsup : (⨆ x, f x) ≤ ((m₀ / c : ℝ) : EReal) := iSup_le hall
      calc ((c : ℝ) : EReal) * (⨆ x, f x)
          ≤ ((c : ℝ) : EReal) * ((m₀ / c : ℝ) : EReal) :=
            mul_le_mul_of_nonneg_left hsup (EReal.coe_nonneg.mpr hc.le)
        _ = ((m₀ : ℝ) : EReal) := by
            rw [← EReal.coe_mul, mul_div_cancel₀ _ hc.ne']
  · exact iSup_le fun x => mul_le_mul_of_nonneg_left (le_iSup f x) (EReal.coe_nonneg.mpr hc.le)

private lemma ereal_add_iSup {ι : Type*} [Nonempty ι] (a : ℝ) (f : ι → EReal) :
    ((a : ℝ) : EReal) + (⨆ x, f x) = ⨆ x, (((a : ℝ) : EReal) + f x) := by
  apply le_antisymm
  · set M : EReal := ⨆ x, (((a : ℝ) : EReal) + f x)
    cases hM : M with
    | top => exact le_top
    | bot =>
      have hall : ∀ x, f x = ⊥ := by
        intro x
        have hx : ((a : ℝ) : EReal) + f x ≤ ⊥ := hM ▸ le_iSup (fun y => ((a : ℝ) : EReal) + f y) x
        have hxeq : ((a : ℝ) : EReal) + f x = ⊥ := le_bot_iff.mp hx
        cases hfx : f x with
        | bot => rfl
        | coe r =>
          rw [hfx, ← EReal.coe_add] at hxeq
          exact absurd hxeq (EReal.coe_ne_bot _)
        | top =>
          rw [hfx, EReal.coe_add_top] at hxeq
          exact absurd hxeq top_ne_bot
      have hsup : (⨆ x, f x) = ⊥ := iSup_eq_bot.mpr hall
      rw [hsup, EReal.add_bot]
    | coe m₀ =>
      have hall : ∀ x, f x ≤ ((m₀ - a : ℝ) : EReal) := by
        intro x
        have hx : ((a : ℝ) : EReal) + f x ≤ ((m₀ : ℝ) : EReal) :=
          hM ▸ le_iSup (fun y => ((a : ℝ) : EReal) + f y) x
        cases hfx : f x with
        | bot => exact bot_le
        | coe r =>
          rw [hfx, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx
          exact EReal.coe_le_coe_iff.mpr (by linarith)
        | top =>
          rw [hfx, EReal.coe_add_top] at hx
          exact absurd (top_le_iff.mp hx) (EReal.coe_ne_top _)
      have hsup : (⨆ x, f x) ≤ ((m₀ - a : ℝ) : EReal) := iSup_le hall
      calc ((a : ℝ) : EReal) + (⨆ x, f x)
          ≤ ((a : ℝ) : EReal) + ((m₀ - a : ℝ) : EReal) := add_le_add le_rfl hsup
        _ = ((m₀ : ℝ) : EReal) := by rw [← EReal.coe_add, add_sub_cancel]
  · exact iSup_le fun x => add_le_add le_rfl (le_iSup f x)

private lemma ftc_line {m l r : ℕ} (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θs : Fin l → ℝ) (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (w_i Δ : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ u in (0 : ℝ)..1, fderiv ℝ (fun x => h x θs) (w_i + c • (u • Δ)) Δ =
      c⁻¹ • (h (w_i + c • Δ) θs - h w_i θs) := by
  set g : ℝ → (Fin r → ℝ) := fun u => fderiv ℝ (fun x => h x θs) (w_i + c • (u • Δ)) Δ
  have hg_cont : Continuous g := by
    have hfderiv : Continuous (fun x : Fin m → ℝ => fderiv ℝ (fun y => h y θs) x) :=
      hC1.continuous_fderiv one_ne_zero
    have hpath : Continuous (fun u : ℝ => w_i + c • (u • Δ)) := by fun_prop
    exact (ContinuousLinearMap.apply ℝ (Fin r → ℝ) Δ).continuous.comp (hfderiv.comp hpath)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (w_i + t • (c • Δ)) θs) (c • g u) u := by
    intro u _
    have hline : HasDerivAt (fun t : ℝ => w_i + t • (c • Δ)) (c • Δ) u := by
      rw [hasDerivAt_pi]
      intro k
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, id_eq] using
        ((hasDerivAt_id u).mul_const (c * Δ k)).const_add (w_i k)
    have hf : HasFDerivAt (fun x => h x θs)
        (fderiv ℝ (fun x => h x θs) (w_i + u • (c • Δ))) (w_i + u • (c • Δ)) :=
      (hC1.differentiable one_ne_zero _).hasFDerivAt
    have hcomp := hf.comp_hasDerivAt u hline
    exact hcomp.congr_deriv (by simp only [g, smul_comm c u Δ, map_smul])
  have hint : IntervalIntegrable (fun u => c • g u) volume 0 1 :=
    (hg_cont.const_smul c).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_smul] at hftc
  simp only [one_smul, zero_smul, add_zero] at hftc
  calc ∫ u in (0 : ℝ)..1, g u = c⁻¹ • (c • ∫ u in (0 : ℝ)..1, g u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • (h (w_i + c • Δ) θs - h w_i θs) := by rw [hftc]

end SolRWPILimitEq3132

theorem solution {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (hw : Function.Injective w)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q : ENNReal) (hq : 1 < q)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θs))) :
    ((ENNReal.ofReal ((n : ℝ) ^ (ρ / 2)) *
        rwp (costQ q ρ) h θs (WassersteinDRO.Regularization.empiricalDistribution w) : ENNReal)
        : EReal) =
      ⨆ ζ : Fin r → ℝ, (((-(ζ ⬝ᵥ Hn h θs w)) : ℝ) : EReal) - Mn q ρ h θs w ζ := by
  have : Fact (1 ≤ q) := ⟨hq.le⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hρ_pos : 0 < ρ := zero_lt_one.trans_le hρ
  set s : ℝ := (n : ℝ) ^ (ρ / 2)
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hn_pos _
  set sqn : ℝ := Real.sqrt (n : ℝ)
  have hsqn_pos : 0 < sqn := Real.sqrt_pos.mpr hn_pos
  have hc_cont : Continuous (Function.uncurry (@costQ m q ρ)) := by
    have hnorm_cont : Continuous (fun uv : (Fin m → ℝ) × (Fin m → ℝ) =>
        ‖WithLp.toLp q (uv.2 - uv.1)‖ ^ ρ) :=
      (continuous_norm.comp ((PiLp.continuous_toLp q _).comp
        (continuous_snd.sub continuous_fst))).rpow_const (fun _ => Or.inr hρ_pos.le)
    exact ENNReal.continuous_ofReal.comp hnorm_cont
  have hc_diag : ∀ u : Fin m → ℝ, costQ q ρ u u = 0 := by
    intro u
    simp [costQ, Real.zero_rpow hρ_pos.ne']
  have hc_fin : ∀ u v : Fin m → ℝ, costQ q ρ u v ≠ ⊤ := fun _ _ => ENNReal.ofReal_ne_top
  have hprop3 := RWPI.Limit.proposition_3 hn w hw (costQ q ρ) hc_cont.lowerSemicontinuous
    hc_diag hc_fin h θs hC1.continuous.measurable hint
  set R := rwp (costQ q ρ) h θs (empiricalDistribution w)
  have hlhs_mul : ((ENNReal.ofReal s * R : ℝ≥0∞) : EReal) = ((s : ℝ) : EReal) * (R : EReal) := by
    rcases eq_or_ne R ⊤ with hR_top | hR_top
    · have hs_ne0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs_pos).ne'
      rw [hR_top, ENNReal.mul_top hs_ne0, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hs_pos]
    · conv_lhs => rw [← ENNReal.ofReal_toReal hR_top]
      rw [← ENNReal.ofReal_mul hs_pos.le, EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg hs_pos.le ENNReal.toReal_nonneg), EReal.coe_mul]
      congr 1
      conv_rhs => rw [← ENNReal.ofReal_toReal hR_top]
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
  rw [hlhs_mul, hprop3, SolRWPILimitEq3132.ereal_mul_iSup_of_pos hs_pos]
  let lamEquiv : (Fin r → ℝ) ≃ (Fin r → ℝ) :=
    { toFun := fun ζ => (sqn / s) • ζ
      invFun := fun lam => (s / sqn) • lam
      left_inv := fun ζ => by
        dsimp only
        rw [smul_smul, show s / sqn * (sqn / s) = 1 by field_simp [hs_pos.ne', hsqn_pos.ne'],
          one_smul]
      right_inv := fun lam => by
        dsimp only
        rw [smul_smul, show sqn / s * (s / sqn) = 1 by field_simp [hs_pos.ne', hsqn_pos.ne'],
          one_smul] }
  rw [← lamEquiv.iSup_comp]
  refine iSup_congr fun ζ => ?_
  set lam : Fin r → ℝ := lamEquiv ζ
  set S : Fin n → EReal := fun i =>
    ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u (w i) : EReal))
  set T : Fin n → EReal := fun i =>
    ⨆ Δ : Fin m → ℝ,
      (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
          fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ)
        - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)
  have hS_ne_bot : ∀ i : Fin n, S i ≠ ⊥ := by
    intro i
    have hle : (((lam ⬝ᵥ h (w i) θs : ℝ) : EReal) - (costQ q ρ (w i) (w i) : EReal)) ≤ S i :=
      le_iSup (fun u : Fin m → ℝ =>
        (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u (w i) : EReal))) (w i)
    rw [hc_diag (w i)] at hle
    have hnb : (((lam ⬝ᵥ h (w i) θs : ℝ) : EReal) - (0 : ℝ≥0∞)) ≠ ⊥ := by simp
    intro heq; rw [heq] at hle; exact hnb (le_bot_iff.mp hle)
  have hT_ne_bot : ∀ i : Fin n, T i ≠ ⊥ := by
    intro i
    have hle : (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
          fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • (0 : Fin m → ℝ))) (0 : Fin m → ℝ))
        - ‖WithLp.toLp q (0 : Fin m → ℝ)‖ ^ ρ : ℝ) : EReal) ≤ T i :=
      le_iSup (fun Δ : Fin m → ℝ =>
        (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
            fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ)
          - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)) 0
    intro heq; rw [heq] at hle
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
  have hTS_rel : ∀ i : Fin n,
      T i = ((-(sqn * (ζ ⬝ᵥ h (w i) θs)) : ℝ) : EReal) + ((s : ℝ) : EReal) * S i := by
    intro i
    let uEquiv : (Fin m → ℝ) ≃ (Fin m → ℝ) :=
      { toFun := fun Δ => w i + sqn⁻¹ • Δ
        invFun := fun u => sqn • (u - w i)
        left_inv := fun Δ => by
          dsimp only
          rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsqn_pos.ne', one_smul]
        right_inv := fun u => by
          dsimp only
          rw [smul_smul, inv_mul_cancel₀ hsqn_pos.ne', one_smul, add_sub_cancel] }
    have hS_rw : S i = ⨆ Δ : Fin m → ℝ,
        (((lam ⬝ᵥ h (uEquiv Δ) θs - ‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ : ℝ) : EReal)) := by
      dsimp only [S]
      rw [← uEquiv.iSup_comp]
      refine iSup_congr fun Δ => ?_
      have hcost : (costQ q ρ (uEquiv Δ) (w i) : EReal) =
          (((‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ : ℝ) : EReal)) := by
        unfold costQ
        rw [EReal.coe_ennreal_ofReal, max_eq_left (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [hcost, ← EReal.coe_sub]
    rw [hS_rw, SolRWPILimitEq3132.ereal_mul_iSup_of_pos hs_pos, SolRWPILimitEq3132.ereal_add_iSup]
    refine iSup_congr fun Δ => ?_
    rw [← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have hftc := SolRWPILimitEq3132.ftc_line h θs hC1 (w i) Δ (inv_ne_zero hsqn_pos.ne')
    rw [inv_inv] at hftc
    have hdot_ftc : ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ =
        sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs - ζ ⬝ᵥ h (w i) θs) := by
      rw [hftc, dotProduct_smul, smul_eq_mul, dotProduct_sub]
      rfl
    have hlam_dot : s * (lam ⬝ᵥ h (uEquiv Δ) θs) = sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs) := by
      change s * (((sqn / s) • ζ) ⬝ᵥ h (uEquiv Δ) θs) = sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs)
      rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_div_cancel₀ _ hs_pos.ne']
    have hnorm_diff : w i - uEquiv Δ = -(sqn⁻¹ • Δ) := by
      dsimp [uEquiv]; abel
    have hcost_scale : s * ‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ = ‖WithLp.toLp q Δ‖ ^ ρ := by
      rw [hnorm_diff]
      have hnorm_smul : ‖WithLp.toLp q (-(sqn⁻¹ • Δ))‖ = sqn⁻¹ * ‖WithLp.toLp q Δ‖ := by
        change ‖-(sqn⁻¹ • WithLp.toLp q Δ)‖ = sqn⁻¹ * ‖WithLp.toLp q Δ‖
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqn_pos)]
      rw [hnorm_smul, Real.mul_rpow (inv_nonneg.mpr hsqn_pos.le) (norm_nonneg _)]
      have hsqn_rpow : s * (sqn⁻¹) ^ ρ = 1 := by
        dsimp [s, sqn]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn_pos.le, ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_add hn_pos]
        have hexp : ρ / 2 + -(1 / 2) * ρ = 0 := by ring
        rw [hexp, Real.rpow_zero]
      rw [← mul_assoc, hsqn_rpow, one_mul]
    rw [hdot_ftc]
    linarith [hlam_dot, hcost_scale]
  by_cases htop : ∃ i₀ : Fin n, S i₀ = ⊤
  · obtain ⟨i₀, hi₀⟩ := htop
    have hTi₀ : T i₀ = ⊤ := by
      rw [hTS_rel i₀, hi₀, EReal.coe_mul_top_of_pos hs_pos, EReal.coe_add_top]
    have hsumS : ∑ i : Fin n, S i = ⊤ := by
      classical
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hi₀]
      exact EReal.top_add_of_ne_bot
        (SolRWPILimitEq3132.finset_sum_ne_bot _ _ fun i _ => hS_ne_bot i)
    have hsumT : ∑ i : Fin n, T i = ⊤ := by
      classical
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hTi₀]
      exact EReal.top_add_of_ne_bot
        (SolRWPILimitEq3132.finset_sum_ne_bot _ _ fun i _ => hT_ne_bot i)
    have hMn_top : Mn q ρ h θs w ζ = ⊤ := by
      dsimp [Mn]
      change ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, T i = ⊤
      rw [hsumT, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos)]
    rw [hsumS, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos), EReal.neg_top,
      EReal.coe_mul_bot_of_pos hs_pos, hMn_top]
    rfl
  · push Not at htop
    set sv : Fin n → ℝ := fun i => (S i).toReal
    have hS_eq : ∀ i : Fin n, S i = ((sv i : ℝ) : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hS_ne_bot i)).symm
    have hT_eq : ∀ i : Fin n, T i = ((-(sqn * (ζ ⬝ᵥ h (w i) θs)) + s * sv i : ℝ) : EReal) := by
      intro i
      rw [hTS_rel i, hS_eq i, ← EReal.coe_mul, ← EReal.coe_add]
    have hMn_eq : Mn q ρ h θs w ζ =
        (((1 / (n : ℝ)) * ∑ i : Fin n, (-(sqn * (ζ ⬝ᵥ h (w i) θs)) + s * sv i) : ℝ) : EReal) := by
      dsimp [Mn]
      change ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, T i = _
      simp_rw [hT_eq]
      rw [SolRWPILimitEq3132.finset_sum_coe_ereal, ← EReal.coe_mul]
    change ((s : ℝ) : EReal) * -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, S i) =
      (((-(ζ ⬝ᵥ Hn h θs w)) : ℝ) : EReal) - Mn q ρ h θs w ζ
    simp_rw [hS_eq]
    rw [SolRWPILimitEq3132.finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_mul,
      hMn_eq, ← EReal.coe_sub]
    congr 1
    have hHn : ζ ⬝ᵥ Hn h θs w = sqn⁻¹ * ∑ i : Fin n, ζ ⬝ᵥ h (w i) θs := by
      dsimp [Hn]
      rw [dotProduct_smul, smul_eq_mul, dotProduct_sum]
    have hsqn_div : (1 / (n : ℝ)) * sqn = sqn⁻¹ := by
      have hsq : sqn * sqn = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      field_simp [hn_pos.ne', hsqn_pos.ne']
      linarith
    rw [hHn, Finset.sum_add_distrib]
    have hsum1 : ∑ i : Fin n, -(sqn * (ζ ⬝ᵥ h (w i) θs)) = -sqn * ∑ i : Fin n, ζ ⬝ᵥ h (w i) θs := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hsum2 : ∑ i : Fin n, s * sv i = s * ∑ i : Fin n, sv i := (Finset.mul_sum _ _ _).symm
    rw [hsum1, hsum2, mul_add, ← mul_assoc, ← mul_assoc]
    have h1 : (1 / (n : ℝ)) * -sqn = -sqn⁻¹ := by linarith [hsqn_div]
    rw [h1]
    ring
