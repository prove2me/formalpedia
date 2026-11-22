-- Prove2me | solution 1 for PolyInverseEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:17:26.621123+00:00
-- url     : https://prove2.me/submissions/8ab1043d-2aca-4b47-abad-cf12097e098d

import Definitions.Def_PHigherOrder_PolyDiagonalJetRigidity
import Definitions.Def_PHigherOrder_VanishingOnUnitBallKillsJets
import Definitions.Def_PHigherOrder_PolyInverseEstimate
import Theorems.Thm_PolyDiagonalJetRigidity
import Theorems.Thm_VanishingOnUnitBallKillsJets


set_option autoImplicit false

theorem _root_.solution (k : ℕ) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ R : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) R →
      (∀ x : Plane, iteratedFDeriv ℝ (k + 1) R x = 0) →
      ∀ (z : Plane) (d A : ℝ), 0 < d → 0 ≤ A →
      (∀ y ∈ Metric.ball z d, |R y| ≤ A) →
      ‖iteratedFDeriv ℝ k R z‖ ≤ Ck * A / d ^ k := by
  -- the closed unit ball is a compact space, so `C(closedBall 0 1, ℝ)` is normed (3a)
  have hKcpt : CompactSpace (Metric.closedBall (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  -- each space `V_j` of continuous `j`-linear forms is finite dimensional
  have hfd : ∀ j : ℕ,
      FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℝ) := by
    intro j
    induction j with
    | zero =>
        exact (continuousMultilinearCurryFin0 ℝ Plane ℝ).toLinearEquiv.symm.finiteDimensional
    | succ n ih =>
        have := ih
        exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Plane)
          ℝ).toLinearEquiv.symm.finiteDimensional
  -- Step 1: `P_k` is a linear subspace of the smooth functions
  obtain ⟨Pk, hPk⟩ : ∃ P : Submodule ℝ (Plane → ℝ), ∀ S : Plane → ℝ,
      S ∈ P ↔ (ContDiff ℝ (⊤ : ℕ∞) S ∧ ∀ w : Plane, iteratedFDeriv ℝ (k + 1) S w = 0) := by
    refine ⟨{ carrier := {S : Plane → ℝ | ContDiff ℝ (⊤ : ℕ∞) S ∧
                  ∀ w : Plane, iteratedFDeriv ℝ (k + 1) S w = 0}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun _ => Iff.rfl⟩
    · rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
      refine ⟨hf.add hg, fun w => ?_⟩
      rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
        (hg.contDiffAt.of_le (by exact_mod_cast le_top)), hf0 w, hg0 w, add_zero]
    · refine ⟨contDiff_const, fun w => ?_⟩
      have h0 : (0 : Plane → ℝ) = fun _ : Plane => (0 : ℝ) := rfl
      rw [h0, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
      rfl
    · rintro c f ⟨hf, hf0⟩
      refine ⟨hf.const_smul c, fun w => ?_⟩
      rw [iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)),
        hf0 w, smul_zero]
  have hsm : ∀ S : Pk, ContDiff ℝ (⊤ : ℕ∞) ((S : Plane → ℝ)) := fun S => ((hPk _).mp S.2).1
  have htp : ∀ (S : Pk) (w : Plane), iteratedFDeriv ℝ (k + 1) ((S : Plane → ℝ)) w = 0 :=
    fun S => ((hPk _).mp S.2).2
  have hat : ∀ (S : Pk) (n : ℕ) (x : Plane), ContDiffAt ℝ (n : ℕ∞) ((S : Plane → ℝ)) x :=
    fun S n x => (hsm S).contDiffAt.of_le (by exact_mod_cast le_top)
  -- Step 2: the jet map `Φ` is linear and injective, so `P_k` is finite dimensional
  obtain ⟨Φ, hΦ⟩ : ∃ F : Pk →ₗ[ℝ] ((j : Fin (k + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => Plane) ℝ),
      ∀ (S : Pk) (j : Fin (k + 1)), F S j = iteratedFDeriv ℝ (j : ℕ) ((S : Plane → ℝ)) 0 := by
    refine ⟨{ toFun := fun S j => iteratedFDeriv ℝ (j : ℕ) ((S : Plane → ℝ)) 0
              map_add' := ?_
              map_smul' := ?_ }, fun _ _ => rfl⟩
    · intro S T
      funext j
      exact iteratedFDeriv_add_apply (hat S j 0) (hat T j 0)
    · intro c S
      funext j
      exact iteratedFDeriv_const_smul_apply (hat S j 0)
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun S hS => ?_
    have hjets : ∀ j : ℕ, j ≤ k → ∀ w : Plane,
        iteratedFDeriv ℝ j ((S : Plane → ℝ)) 0 (fun _ => w) = 0 := by
      intro j hj w
      have hz : iteratedFDeriv ℝ j ((S : Plane → ℝ)) 0 = 0 := by
        have := congrFun hS (⟨j, by omega⟩ : Fin (k + 1))
        rw [hΦ S ⟨j, by omega⟩] at this
        simpa using this
      rw [hz]
      rfl
    exact Subtype.ext (PolyDiagonalJetRigidity k _ (hsm S) (htp S) hjets)
  have hPkfd : FiniteDimensional ℝ Pk := FiniteDimensional.of_injective Φ hΦinj
  -- Step 3: `N(S) = sup_{|w| ≤ 1} |S(w)|` is the norm of the restriction of `S` to the closed
  -- unit ball as a bounded continuous function; (3a) that restriction is bounded because the
  -- closed unit ball is compact, (3b) `N` is a seminorm because it is the sup norm, and
  -- (3c) `N` is definite because the restriction map is injective
  obtain ⟨Θ, hΘ⟩ : ∃ F : Pk →ₗ[ℝ]
        BoundedContinuousFunction (Metric.closedBall (0 : Plane) 1) ℝ,
      ∀ (S : Pk) (w : Metric.closedBall (0 : Plane) 1),
        F S w = (S : Plane → ℝ) (w : Plane) := by
    refine ⟨{ toFun := fun S => BoundedContinuousFunction.mkOfCompact
                  ⟨fun w => (S : Plane → ℝ) (w : Plane),
                    (hsm S).continuous.comp continuous_subtype_val⟩
              map_add' := fun S T => rfl
              map_smul' := fun c S => rfl }, fun _ _ => rfl⟩
  have hΘinj : Function.Injective Θ := by
    refine (injective_iff_map_eq_zero Θ).mpr fun S hS => ?_
    have hvan : ∀ w : Plane, ‖w‖ ≤ 1 → (S : Plane → ℝ) w = 0 := by
      intro w hw
      have hwmem : w ∈ Metric.closedBall (0 : Plane) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hw
      have h0 : Θ S ⟨w, hwmem⟩ = 0 := by rw [hS]; simp
      rw [hΘ S ⟨w, hwmem⟩] at h0
      exact h0
    exact Subtype.ext (PolyDiagonalJetRigidity k _ (hsm S) (htp S)
      (fun j _ w => VanishingOnUnitBallKillsJets _ (hsm S) hvan j w))
  -- Step 4: the estimate at the normalized scale
  obtain ⟨L, hL⟩ : ∃ G : Pk →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Plane) ℝ,
      ∀ S : Pk, G S = iteratedFDeriv ℝ k ((S : Plane → ℝ)) 0 := by
    refine ⟨{ toFun := fun S => iteratedFDeriv ℝ k ((S : Plane → ℝ)) 0
              map_add' := fun S T => iteratedFDeriv_add_apply (hat S k 0) (hat T k 0)
              map_smul' := fun c S => iteratedFDeriv_const_smul_apply (hat S k 0) },
      fun _ => rfl⟩
  obtain ⟨Λ, hΛ0, hΛ⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ S : Pk, ‖L S‖ ≤ Λ * ‖Θ S‖ := by
    -- read `P_k` in linear coordinates, which is legitimate because it is finite dimensional
    have φ : (Fin (Module.finrank ℝ Pk) → ℝ) ≃ₗ[ℝ] Pk := (Module.finBasis ℝ Pk).equivFun.symm
    -- `Θ` is injective, hence antilipschitz in these coordinates: this is the inverse bound
    have hinj : Function.Injective (Θ.comp φ.toLinearMap) :=
      fun a b hab => φ.injective (hΘinj hab)
    obtain ⟨C, hC0, hC⟩ := (Θ.comp φ.toLinearMap).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hinj)
    have hlow : ∀ v : Fin (Module.finrank ℝ Pk) → ℝ, ‖v‖ ≤ (C : ℝ) * ‖Θ (φ v)‖ := by
      intro v
      simpa [dist_eq_norm] using hC.le_mul_dist v 0
    -- `L` is a linear map out of a finite-dimensional normed space, hence bounded
    obtain ⟨Λ₀, hΛ₀0, hΛ₀⟩ : ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
        ∀ v : Fin (Module.finrank ℝ Pk) → ℝ, ‖L (φ v)‖ ≤ Λ₀ * ‖v‖ := by
      refine ⟨‖(⟨L.comp φ.toLinearMap, (L.comp φ.toLinearMap).continuous_of_finiteDimensional⟩ :
          (Fin (Module.finrank ℝ Pk) → ℝ) →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin k => Plane) ℝ)‖,
        ContinuousLinearMap.opNorm_nonneg _, fun v => ?_⟩
      simpa using (⟨L.comp φ.toLinearMap,
        (L.comp φ.toLinearMap).continuous_of_finiteDimensional⟩ :
          (Fin (Module.finrank ℝ Pk) → ℝ) →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin k => Plane) ℝ).le_opNorm v
    refine ⟨Λ₀ * (C : ℝ), mul_nonneg hΛ₀0 (NNReal.coe_nonneg C), fun S => ?_⟩
    have h1 := hΛ₀ (φ.symm S)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h3 := hlow (φ.symm S)
    rw [LinearEquiv.apply_symm_apply] at h3
    calc ‖L S‖ ≤ Λ₀ * ‖φ.symm S‖ := h1
      _ ≤ Λ₀ * ((C : ℝ) * ‖Θ S‖) := mul_le_mul_of_nonneg_left h3 hΛ₀0
      _ = Λ₀ * (C : ℝ) * ‖Θ S‖ := by ring
  refine ⟨Λ + 1, by linarith, ?_⟩
  -- Step 5: rescaling
  intro R hR htopR z d A hd hA hbd
  have hdk : (0 : ℝ) < d ^ k := by positivity
  -- (d) the bound on the open ball extends to the closed ball, by continuity
  have hbdcl : ∀ y ∈ Metric.closedBall z d, |R y| ≤ A := by
    have hcl : Metric.closedBall z d ⊆ {y : Plane | |R y| ≤ A} := by
      rw [← closure_ball z (ne_of_gt hd)]
      exact closure_minimal hbd
        (isClosed_le (continuous_abs.comp hR.continuous) continuous_const)
    exact fun y hy => hcl hy
  obtain ⟨S, hSdef⟩ : ∃ S : Plane → ℝ, S = fun w : Plane => R (d • w + z) := ⟨_, rfl⟩
  have hSval : ∀ v : Plane, S v = R (d • v + z) := fun v => by rw [hSdef]
  -- (a) `S` is smooth, as is the translate `R(· + z)`
  have hRz : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane => R (y + z)) :=
    hR.comp (contDiff_id.add contDiff_const)
  have hSsm : ContDiff ℝ (⊤ : ℕ∞) S := by
    rw [hSdef]
    exact hR.comp ((contDiff_id.const_smul d).add contDiff_const)
  -- (b) the scaling identity for the iterated derivatives
  have hjet : ∀ (n : ℕ) (w : Plane),
      iteratedFDeriv ℝ n S w = d ^ n • iteratedFDeriv ℝ n R (d • w + z) := by
    intro n w
    have hstep : iteratedFDeriv ℝ n (fun v : Plane => (fun y : Plane => R (y + z)) (d • v))
        = fun x : Plane => d ^ n • iteratedFDeriv ℝ n (fun y : Plane => R (y + z)) (d • x) :=
      iteratedFDeriv_comp_const_smul d (hRz.of_le (by exact_mod_cast le_top))
    calc iteratedFDeriv ℝ n S w
        = iteratedFDeriv ℝ n (fun v : Plane => (fun y : Plane => R (y + z)) (d • v)) w := by
            rw [hSdef]
      _ = d ^ n • iteratedFDeriv ℝ n (fun y : Plane => R (y + z)) (d • w) := by
            rw [hstep]
      _ = d ^ n • iteratedFDeriv ℝ n R (d • w + z) := by
            rw [iteratedFDeriv_comp_add_right]
  -- (c) `S ∈ P_k`
  have hSmem : S ∈ Pk := (hPk S).mpr ⟨hSsm, fun w => by
    rw [hjet (k + 1) w, htopR (d • w + z), smul_zero]⟩
  -- (d) `N(S) ≤ A`
  have hNS : ‖Θ ⟨S, hSmem⟩‖ ≤ A := by
    refine (BoundedContinuousFunction.norm_le hA).mpr fun w => ?_
    rw [hΘ ⟨S, hSmem⟩ w, Real.norm_eq_abs]
    show |S (w : Plane)| ≤ A
    rw [hSval]
    refine hbdcl _ ?_
    have hw : ‖(w : Plane)‖ ≤ 1 := by
      have hwm := w.2
      rw [Metric.mem_closedBall, dist_zero_right] at hwm
      exact hwm
    have hdist : ‖d • (w : Plane) + z - z‖ ≤ d := by
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      calc d * ‖(w : Plane)‖ ≤ d * 1 := by
            exact mul_le_mul_of_nonneg_left hw (le_of_lt hd)
        _ = d := by ring
    simpa [Metric.mem_closedBall, dist_eq_norm] using hdist
  -- (e) conclusion
  have hLS : L ⟨S, hSmem⟩ = d ^ k • iteratedFDeriv ℝ k R z := by
    rw [hL ⟨S, hSmem⟩]
    show iteratedFDeriv ℝ k S 0 = _
    rw [hjet k 0, smul_zero, zero_add]
  have hkey : d ^ k * ‖iteratedFDeriv ℝ k R z‖ ≤ Λ * A := by
    have h1 := hΛ ⟨S, hSmem⟩
    rw [hLS, norm_smul, Real.norm_eq_abs, abs_of_pos hdk] at h1
    calc d ^ k * ‖iteratedFDeriv ℝ k R z‖ ≤ Λ * ‖Θ ⟨S, hSmem⟩‖ := h1
      _ ≤ Λ * A := mul_le_mul_of_nonneg_left hNS hΛ0
  rw [le_div_iff₀ hdk]
  nlinarith [hkey, hA, hΛ0]
