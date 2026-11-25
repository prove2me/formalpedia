-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:26.402424+00:00
-- url     : https://prove2.me/submissions/6733b1d7-08cb-4664-ba15-cee13d3d6f44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_secSet_of_sheet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secSet_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsSumMeasurable
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.PtsSumMeasurable
theorem _root_.solution {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    ∃ (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      (∀ m, IsOpen (B m)) ∧
      (∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ mcPts P ∧
        Ψ (segre (γ m y)) = Fin.cons 1 y) ∧
      ∀ y w γ', IsSheet P Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  let Bl : D × ℕ → Set (Fin e → ℂ) := fun p => ball (p.1 : Fin e → ℂ) (1 / (p.2 + 1))
  have : Countable D := hDc.to_subtype
  have : ∀ p : D × ℕ, Countable (secSet P Ψ (Bl p)) := fun p =>
    (secSet_finite osgood hfin (p.1 : Fin e → ℂ) (hρ p.2)).countable.to_subtype
  let T := Σ p : D × ℕ, secSet P Ψ (Bl p)
  let Lift : T → ((Fin e → ℂ) → (Σ k, ι k) → ℂ) → Prop := fun t γ =>
    ∀ y ∈ Bl t.1, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧
      segre (γ y) = (t.2 : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y
  let Bo : Option T → Set (Fin e → ℂ) := fun o =>
    o.elim ∅ fun t => if ∃ γ, Lift t γ then Bl t.1 else ∅
  let γo : Option T → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun o =>
    o.elim (fun _ _ => 0) fun t => if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option T)
  have hBsome : ∀ t : T, Bo (some t) = if ∃ γ, Lift t γ then Bl t.1 else ∅ := fun t => rfl
  have hγsome : ∀ t : T, (h : ∃ γ, Lift t γ) → γo (some t) = h.choose := fun t h => by
    show (if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0) = _
    rw [dif_pos h]
  have hBo : ∀ o, IsOpen (Bo o) := by
    rintro (_ | t)
    · exact isOpen_empty
    · rw [hBsome]
      split_ifs
      · exact isOpen_ball
      · exact isOpen_empty
  have hlift : ∀ o, ∀ y ∈ Bo o, DifferentiableAt ℂ (γo o) y ∧ γo o y ∈ mcPts P ∧
      Ψ (segre (γo o y)) = Fin.cons 1 y := by
    rintro (_ | t) y hy
    · exact absurd hy (Set.notMem_empty y)
    · rw [hBsome] at hy
      split_ifs at hy with h
      · rw [hγsome t h]
        obtain ⟨h1, h2, h3⟩ := h.choose_spec y hy
        refine ⟨h1, h2, ?_⟩
        obtain ⟨-, -, hfib⟩ := t.2.2
        obtain ⟨z, -, -, hΨ⟩ := hfib y hy
        rw [h3, hΨ]
      · exact absurd hy (Set.notMem_empty y)
  refine ⟨fun m => Bo (f m), fun m => γo (f m), fun m => hBo (f m), fun m => hlift (f m),
    fun y w γ' hγ' => ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hγ'.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    let p : D × ℕ := (⟨d, hdD⟩, n)
    have hyB : y ∈ Bl p := by
      show y ∈ ball d (1 / ((n : ℝ) + 1))
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : Bl p ⊆ ball y ε := by
      intro y' hy'
      have hy'' : dist y' d < 1 / ((n : ℝ) + 1) := hy'
      rw [mem_ball] at hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy'' hdy
        _ < ε := by linarith
    have hG := mem_secSet_of_sheet (P := P) (Ψ := Ψ) (B := Bl p) (γ := γ') fun y' hy' =>
      hball y' (hBsub hy')
    let t : T := ⟨p, _, hG⟩
    have hL : ∃ γ, Lift t γ := ⟨γ', fun y' hy' => ⟨(hball y' (hBsub hy')).1,
      (hball y' (hBsub hy')).2.1, by simp only [t]; rw [Set.indicator_of_mem hy']⟩⟩
    obtain ⟨m, hm⟩ := hf (some t)
    refine ⟨m, ?_, ?_⟩
    · show y ∈ Bo (f m)
      rw [hm, hBsome, if_pos hL]
      exact hyB
    · show segre (γo (f m) y) = w
      rw [hm, hγsome t hL, (hL.choose_spec y hyB).2.2]
      simp only [t]
      rw [Set.indicator_of_mem hyB, hγ'.1]
end GroundTheory.Heights₂.Heights.PtsSumMeasurable
