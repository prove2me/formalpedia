-- Prove2me | solution 1 for PositivityTheory.KReal.cas_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:34.602897+00:00
-- url     : https://prove2.me/submissions/5b2997f1-e859-4b35-9702-cd39f1bde08e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
import Theorems.Thm_PositivityTheory_KReal_sum_upd
import Theorems.Thm_PositivityTheory_KReal_formT_positionA
import Theorems.Thm_PositivityTheory_KReal_formT_self_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {K I J : Type} [Fintype K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J]
    (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (c0 : ℝ) (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (W : (J → I) → Module.End ℂ M)
    (hW : ∀ k w, e k * W w = W w * e k + ∑ i, ∑ j, c k j (w i) • W (Function.update w i j))
    (φ : M →ₗ[ℂ] ℂ) (Ψ : (J → I) → V) (hΨ : ∀ w v, ⟪Ψ w, v⟫_ℂ = φ (W w (ι v)))
    (hφ : ∀ w v, φ ((∑ k, e k * e (σ k)) (W w (ι v)) - (c0 : ℂ) • W w (ι v)) = 0)
    (hpos : ∀ (s : J) (w : J → I),
      0 ≤ (∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re = 0 →
        (fun i => Ψ (Function.update w s i)) = 0)) : Ψ = 0 := by
  have hc : ∀ k u x, e k (W u x) = W u (e k x) + ∑ i, ∑ j, c k j (u i) • W (Function.update u i j) x := by
    intro k u x
    have h := LinearMap.congr_fun (hW k u) x
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have hk : ∀ k u x, e k (e (σ k) (W u x)) = W u (e k (e (σ k) x)) +
      (∑ i, ∑ j, c k j (u i) • W (Function.update u i j) (e (σ k) x) +
        ∑ i, ∑ j, c (σ k) j (u i) • (W (Function.update u i j) (e k x) +
          ∑ i', ∑ j', c k j' (Function.update u i j i') •
            W (Function.update (Function.update u i j) i' j') x)) := by
    intro k u x
    simp only [hc, map_add, map_sum, map_smul, add_assoc]
  have hΨ' : ∀ u v, φ (W u (ι v)) = ⟪Ψ u, v⟫_ℂ := fun u v => (hΨ u v).symm
  have hΨe : ∀ k u v, φ (W u (e k (ι v))) = ⟪Ψ u, ρ k v⟫_ℂ := by
    intro k u v
    rw [← hι, hΨ]
  have hcas : ∀ v, ∑ k, e k (e (σ k) (ι v)) = (c0 : ℂ) • ι v := by
    intro v
    have h := congrArg ι (LinearMap.congr_fun hc0 v)
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, hι, LinearMap.smul_apply,
      Module.End.one_apply, map_smul] using h
  have hA : ∀ u v, ∑ k, φ (W u (e k (e (σ k) (ι v)))) = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by
    intro u v
    calc ∑ k, φ (W u (e k (e (σ k) (ι v)))) = φ (W u (∑ k, e k (e (σ k) (ι v)))) := by
          simp only [map_sum]
      _ = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by rw [hcas, map_smul, map_smul, hΨ', smul_eq_mul]
  have hF : ∀ w, ∑ k, (⟪PositivityTheory.KReal.positionA (c (σ k)) Ψ w, ρ (σ k) (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) Ψ w, ρ k (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ) w, Ψ w⟫_ℂ) = 0 := by
    intro w
    have h := hφ w (Ψ w)
    have h' := hA w (Ψ w)
    simp only [map_sub, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hk, map_add, map_smul,
      smul_eq_mul, hΨ', hΨe, h3, Matrix.conjTranspose_apply, starRingEnd_apply, star_star,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h
    simp only [PositivityTheory.KReal.positionA, sum_inner, inner_smul_left, h3, Matrix.conjTranspose_apply,
      starRingEnd_apply, star_star, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    linear_combination h - h'
  have hsum : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun w _ => hF w)
    rw [Finset.sum_comm] at h
    simpa only [PositivityTheory.KReal.formT, Finset.sum_add_distrib] using h
  have hT1 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) =
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) :=
    Fintype.sum_equiv (Function.Involutive.toPerm σ hσ) _ _ (fun _ => rfl)
  have hck : ∀ k, c k = (c (σ k))ᴴ := fun k => by rw [← h3 (σ k), hσ k]
  have hT3 : 0 ≤ (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k)
      (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [hck k, PositivityTheory.KReal.formT_positionA]
    exact PositivityTheory.KReal.formT_self_nonneg _
  have hre2 : (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re ≤ 0 := by
    have h := congrArg Complex.re hsum
    rw [hT1, Complex.add_re, Complex.add_re, Complex.zero_re] at h
    linarith
  obtain ⟨q, hq⟩ : ∃ q : J → (J → I) → ℂ, ∀ s w, q s w = ∑ k, ∑ i, ∑ j,
      ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : J → (J → I) → ℂ, ∀ s w, H s w = ∑ k, ∑ j,
      ⟪Ψ w, c k (w s) j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  have hpos' : ∀ s w, 0 ≤ (q s w).re ∧ ((q s w).re = 0 → (fun i => Ψ (Function.update w s i)) = 0) := by
    intro s w
    rw [hq]
    exact hpos s w
  have hqH : ∀ s w, q s w = ∑ i, H s (Function.update w s i) := by
    intro s w
    simp only [hq, hH, Function.update_self, Function.update_idem]
    exact Finset.sum_comm
  have hsumH : ∀ s, ∑ w, q s w = (Fintype.card I : ℂ) * ∑ w, H s w := by
    intro s
    have h := PositivityTheory.KReal.sum_upd s (fun w i => H s (Function.update w s i))
    simp only [Function.update_idem, Function.update_eq_self] at h
    simp only [hqH, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hHc : ∀ s w, H s w = starRingEnd ℂ (∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
      ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
    intro s w
    rw [hH]
    simp only [map_sum, map_mul, Complex.conj_conj, inner_conj_symm, inner_smul_right, ← hadj]
  have hT2 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) =
      ∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) * ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ := by
    simp only [PositivityTheory.KReal.formT, PositivityTheory.KReal.positionA, sum_inner, inner_smul_left]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have hHT : (∑ s, ∑ w, H s w).re =
      (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re := by
    rw [hT2, Finset.sum_comm]
    have e1 : ∑ w, ∑ s, H s w = starRingEnd ℂ (∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
        ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
      simp only [hHc, map_sum]
    rw [e1, Complex.conj_re]
  have hQle : ∑ s, ∑ w, (q s w).re ≤ 0 := by
    have e2 : ∑ s, ∑ w, (q s w).re = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
      calc ∑ s, ∑ w, (q s w).re = ∑ s, ((Fintype.card I : ℂ) * ∑ w, H s w).re := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Complex.re_sum, hsumH]
        _ = ((Fintype.card I : ℂ) * ∑ s, ∑ w, H s w).re := by
            rw [Finset.mul_sum, Complex.re_sum]
        _ = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
            rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e2, hHT]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hre2
  have hQ0 : ∀ s w, (q s w).re = 0 := by
    intro s w
    have h1 : (q s w).re ≤ ∑ w', (q s w').re :=
      Finset.single_le_sum (f := fun w' => (q s w').re) (fun w' _ => (hpos' s w').1) (Finset.mem_univ w)
    have h2 : ∑ w', (q s w').re ≤ ∑ s', ∑ w', (q s' w').re :=
      Finset.single_le_sum (f := fun s' => ∑ w', (q s' w').re)
        (fun s' _ => Finset.sum_nonneg fun w' _ => (hpos' s' w').1) (Finset.mem_univ s)
    linarith [(hpos' s w).1]
  funext w
  have h := congrFun ((hpos' (Classical.arbitrary J) w).2 (hQ0 _ w)) (w (Classical.arbitrary J))
  simpa using h
end PositivityTheory.KReal
