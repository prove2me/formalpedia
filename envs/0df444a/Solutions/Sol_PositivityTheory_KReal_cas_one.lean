-- Prove2me | solution 1 for PositivityTheory.KReal.cas_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:49.217853+00:00
-- url     : https://prove2.me/submissions/3614f244-95d9-4b4d-b5c1-808e14ff9178

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
import Theorems.Thm_PositivityTheory_KReal_pos_of_eig
import Theorems.Thm_PositivityTheory_KReal_valOp_apply
import Theorems.Thm_PositivityTheory_KReal_matOp_adj

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
theorem _root_.solution {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (Φ : I → V) (hΦ : ∀ Θ : I → V, ∑ i, X i (ι (Θ i)) = 0 → ∑ i, ⟪Φ i, Θ i⟫_ℂ = 0) :
    0 ≤ (∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re = 0 → Φ = 0) := by
  let R : K → Module.End ℂ (PiLp 2 (fun _ : I => V)) := fun k => matOp (c k) + valOp (ρ k)
  have hRa : ∀ k Θ i, R k Θ i = ∑ j, c k i j • Θ j + ρ k (Θ i) := fun k Θ i => rfl
  have hRadj : ∀ k x y, ⟪R k x, y⟫_ℂ = ⟪x, R (σ k) y⟫_ℂ := by
    intro k x y
    simp only [R, LinearMap.add_apply, inner_add_left, inner_add_right]
    rw [matOp_adj, h3]
    congr 1
    simp only [PiLp.inner_apply, valOp_apply, hadj]
  let m1 : PiLp 2 (fun _ : I => V) →ₗ[ℂ] M :=
    { toFun := fun Θ => ∑ i, X i (ι (Θ i))
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.smul_sum] }
  have hm1 : ∀ Θ, m1 Θ = ∑ i, X i (ι (Θ i)) := fun _ => rfl
  have hem : ∀ k Θ, e k (m1 Θ) = m1 (R k Θ) := by
    intro k Θ
    have h1' : ∀ i y, e k (X i y) = ∑ j, c k j i • X j y + X i (e k y) := by
      intro i y
      have := LinearMap.congr_fun (h1 k i) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at this
      rw [← this]; abel
    simp only [hm1, hRa, map_sum, map_add, map_smul, h1', hι, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  let N := (LinearMap.ker m1)ᗮ
  have hRN : ∀ k, ∀ x ∈ N, R k x ∈ N := by
    intro k x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hRadj]
    apply hx
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← hem, hu, map_zero]
  let S : Module.End ℂ (PiLp 2 (fun _ : I => V)) := ∑ k, R k * R (σ k) - ((c0 + d : ℝ) : ℂ) • 1
  have hSa : ∀ x, S x = ∑ k, R k (R (σ k) x) - ((c0 + d : ℝ) : ℂ) • x := by
    intro x
    simp only [S, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  have hS : LinearMap.IsSymmetric S := by
    intro x y
    rw [hSa, hSa, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hRadj, hRadj, hσ]
  have hSN : ∀ x ∈ N, S x ∈ N := by
    intro x hx
    rw [hSa]
    exact N.sub_mem (N.sum_mem fun k _ => hRN _ _ (hRN _ _ hx)) (N.smul_mem _ hx)
  have hΦN : WithLp.toLp 2 Φ ∈ N := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [PiLp.inner_apply]
    exact hΦ (fun i => u i) hu
  have hpos := pos_of_eig (S.restrict hSN) (hS.restrict_invariant hSN) (by
    intro t ht x hx
    have hx' : S x.1 = (t : ℂ) • x.1 := congrArg Subtype.val hx
    have h0 : m1 x.1 = 0 := by
      refine h5 (t + (c0 + d)) (by linarith) _ ?_ ?_
      · rw [hm1]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, _, rfl⟩
      · rw [hSa, sub_eq_iff_eq_add, ← add_smul] at hx'
        rw [LinearMap.sum_apply]
        simp only [Module.End.mul_apply, hem]
        rw [← map_sum, hx', map_smul]
        push_cast
        rfl
    have h2 : ⟪x.1, x.1⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 x.2 _ h0
    exact Subtype.ext (inner_self_eq_zero.1 h2)) ⟨_, hΦN⟩
  have hval : ∀ i, S (WithLp.toLp 2 Φ) i = (2 : ℂ) • ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
    intro i
    have e1 : ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l = (d : ℂ) • Φ i := by
      have : ∀ l, ∑ k, ∑ j, c k i j * c (σ k) j l = (d : ℂ) * (if i = l then 1 else 0) := by
        intro l
        have := congrFun (congrFun h4 i) l
        simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
      calc ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l
          = ∑ k, ∑ l, ∑ j, (c k i j * c (σ k) j l) • Φ l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum, smul_smul]
        _ = ∑ l, (∑ k, ∑ j, c k i j * c (σ k) j l) • Φ l := by
            rw [Finset.sum_comm]
            simp only [Finset.sum_smul]
        _ = (d : ℂ) • Φ i := by simp [this]
    have e2 : ∑ k, ρ k (ρ (σ k) (Φ i)) = (c0 : ℂ) • Φ i := by
      have := LinearMap.congr_fun hc0 (Φ i)
      simpa [LinearMap.sum_apply] using this
    have e3 : ∑ k, ρ k (∑ l, c (σ k) i l • Φ l) = ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
      rw [← Equiv.sum_comp hσ.toPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.Involutive.coe_toPerm, hσ k, map_sum, map_smul]
    have e4 : S (WithLp.toLp 2 Φ) i = ∑ k, R k (R (σ k) (WithLp.toLp 2 Φ)) i - ((c0 + d : ℝ) : ℂ) • Φ i := by
      rw [hSa]
      simp
    rw [e4]
    simp only [hRa, smul_add, map_add, Finset.sum_add_distrib]
    rw [e1, e2, e3, two_smul]
    push_cast
    rw [add_smul]
    abel
  have hin : (⟪(⟨_, hΦN⟩ : N), S.restrict hSN ⟨_, hΦN⟩⟫_ℂ) =
      2 * ∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ := by
    change ⟪WithLp.toLp 2 Φ, S (WithLp.toLp 2 Φ)⟫_ℂ = _
    rw [PiLp.inner_apply, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval, inner_smul_right]
    simp only [inner_sum]
  rw [hin] at hpos
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [h2re] at hpos
  refine ⟨by linarith [hpos.1], fun h0 => ?_⟩
  have := congrArg Subtype.val (hpos.2 (by rw [h0, mul_zero]))
  funext i
  exact congrArg (fun z : PiLp 2 (fun _ : I => V) => z i) this
end PositivityTheory.KReal
