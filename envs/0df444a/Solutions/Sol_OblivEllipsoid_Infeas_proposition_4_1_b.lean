-- Prove2me | solution 1 for OblivEllipsoid.Infeas.proposition_4_1_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:41:35.253222+00:00
-- url     : https://prove2.me/submissions/a1fa13d9-d19b-44d9-ae60-fa5163b6d6f0

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAProp41b

variable {n m : ℕ}

lemma AT_mulVec_apply (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (k : Fin m) :
    (Aᵀ *ᵥ x) k = col A k ⬝ᵥ x := by
  simp [Matrix.mulVec, dotProduct, col, Matrix.transpose_apply]

/-- The slack function `g(x) = min_i (u_i - a_iᵀx)`. -/
noncomputable def g (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨅ i : Fin m, (u i - col A i ⬝ᵥ x)

lemma g_continuous [Nonempty (Fin m)] (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) :
    Continuous (g A u) := by
  have : g A u = fun x => Finset.univ.inf' Finset.univ_nonempty
      (fun i : Fin m => u i - col A i ⬝ᵥ x) := by
    funext x; rw [Finset.inf'_univ_eq_ciInf]; rfl
  rw [this]
  apply Continuous.finset_inf'_apply
  intro i _
  unfold dotProduct
  fun_prop

lemma le_g_iff [Nonempty (Fin m)] (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (x : Fin n → ℝ) (c : ℝ) : c ≤ g A u x ↔ ∀ i, c ≤ u i - col A i ⬝ᵥ x :=
  le_ciInf_iff (Finite.bddBelow_range _)

lemma g_le (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (x : Fin n → ℝ) (i : Fin m) :
    g A u x ≤ u i - col A i ⬝ᵥ x :=
  ciInf_le (Finite.bddBelow_range _) i

/-- Superlevel sets of `g` are bounded (Assumption 1.1). -/
lemma bounded_superlevel (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (hA : Assumption11 A)
    (c : ℝ) : ∃ lo hi : Fin n → ℝ,
      ∀ x, (∀ i, col A i ⬝ᵥ x ≤ u i - c) → x ∈ Set.Icc lo hi := by
  have key : ∀ z : Fin n → ℝ, ∃ M : ℝ, ∀ x, (∀ i, col A i ⬝ᵥ x ≤ u i - c) → z ⬝ᵥ x ≤ M := by
    intro z
    obtain ⟨μ, hμ0, hμ⟩ := hA.1 z
    refine ⟨∑ i, μ i * (u i - c), fun x hx => ?_⟩
    have : z ⬝ᵥ x = ∑ i, μ i * (col A i ⬝ᵥ x) := by
      rw [← hμ, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      simp only [dotProduct, AT_mulVec_apply]
      refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    rw [this]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hμ0 i)
  choose Mp hMp using fun k : Fin n => key (Pi.single k 1)
  choose Mn hMn using fun k : Fin n => key (-(Pi.single k 1))
  refine ⟨fun k => -Mn k, Mp, fun x hx => ⟨fun k => ?_, fun k => ?_⟩⟩
  · have := hMn k x hx
    simp [neg_dotProduct, single_dotProduct] at this
    linarith
  · have := hMp k x hx
    simpa [single_dotProduct] using this

theorem prop41b (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    tau A u = - zStar A u ∧ 0 < tau A u ∧
      IsLeast {θ : ℝ | ∃ x : Fin n → ℝ, IsFeasible A (u + fun _ => θ) x} (tau A u) := by
  -- m ≠ 0
  have hne : Nonempty (Fin m) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hinf ⟨0, fun i => (IsEmpty.false i).elim⟩
  -- every point violates something
  have hneg : ∀ x, g A u x < 0 := by
    intro x
    by_contra hx
    push Not at hx
    apply hinf ⟨x, fun i => ?_⟩
    have := (le_g_iff A u x 0).1 hx i
    rw [AT_mulVec_apply]; linarith
  -- maximizer of g on a compact superlevel set
  set c := g A u 0 with hc
  set K := {x : Fin n → ℝ | c ≤ g A u x} with hK
  obtain ⟨lo, hi, hbox⟩ := bounded_superlevel A u hA c
  have hKsub : K ⊆ Set.Icc lo hi := by
    intro x hx
    apply hbox
    intro i
    have := (le_g_iff A u x c).1 hx i
    linarith
  have hKcl : IsClosed K := isClosed_le continuous_const (g_continuous A u)
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKcl (Metric.isBounded_Icc lo hi |>.subset hKsub)
  have h0K : (0 : Fin n → ℝ) ∈ K := by simp only [hK, Set.mem_setOf_eq, hc, le_refl]
  obtain ⟨xs, hxsK, hxs⟩ := hKc.exists_isMaxOn ⟨0, h0K⟩ (g_continuous A u).continuousOn
  have hmax : ∀ x, g A u x ≤ g A u xs := by
    intro x
    by_cases hx : x ∈ K
    · exact hxs hx
    · simp only [hK, Set.mem_setOf_eq, not_le] at hx
      exact hx.le.trans hxsK
  have hz : zStar A u = g A u xs := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨xs, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hmax x⟩
  have hzneg : zStar A u < 0 := hz ▸ hneg xs
  have htau : tau A u = - zStar A u := abs_of_neg hzneg
  refine ⟨htau, by rw [htau]; linarith, ?_, ?_⟩
  · refine ⟨xs, fun i => ?_⟩
    have := g_le A u xs i
    rw [AT_mulVec_apply]
    simp only [Pi.add_apply]
    rw [htau, hz]; linarith
  · rintro θ ⟨x, hx⟩
    have h1 : -θ ≤ g A u x := by
      rw [le_g_iff]
      intro i
      have := hx i
      rw [AT_mulVec_apply] at this
      simp only [Pi.add_apply] at this
      linarith
    have := hmax x
    rw [htau, hz]; linarith

end OEAProp41b
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    tau A u = - zStar A u ∧ 0 < tau A u ∧
      IsLeast {θ : ℝ | ∃ x : Fin n → ℝ, IsFeasible A (u + fun _ => θ) x} (tau A u) :=
  OblivEllipsoid.Infeas.OEAProp41b.prop41b A u hA hinf
