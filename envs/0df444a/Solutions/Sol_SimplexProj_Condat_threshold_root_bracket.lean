-- Prove2me | solution 1 for SimplexProj.Condat.threshold_root_bracket
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T02:52:09.654379+00:00
-- url     : https://prove2.me/submissions/28923d68-a97d-402b-8bad-de88525557d2

import Init
import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

open scoped BigOperators
namespace CondatRoot
noncomputable def residual {N : ℕ} (y : Fin N → ℝ) (a ρ : ℝ) : ℝ :=
  ∑ i, max (y i-ρ) 0 - a
lemma antitone {N : ℕ} (y : Fin N → ℝ) (a : ℝ) : Antitone (residual y a) := by
  intro ρ σ h
  apply sub_le_sub_right
  exact Finset.sum_le_sum (fun i _ => max_le_max (by linarith) le_rfl)
lemma convex {N : ℕ} (y : Fin N → ℝ) (a : ℝ) : ConvexOn ℝ Set.univ (residual y a) := by
  refine ⟨convex_univ,?_⟩
  intro ρ _ σ _ u v hu hv huv
  have hp (i : Fin N) : max (y i-(u*ρ+v*σ)) 0 ≤
      u*max (y i-ρ) 0 + v*max (y i-σ) 0 := by
    apply max_le
    · calc
        _ = u*(y i-ρ)+v*(y i-σ) := by nlinarith [congrArg (fun t : ℝ => t * y i) huv]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
    · positivity
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hp i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  change residual y a (u*ρ+v*σ) ≤ u*residual y a ρ+v*residual y a σ
  unfold residual
  nlinarith [congrArg (fun t : ℝ => t * a) huv]
lemma affine_interval {N : ℕ} (y : Fin N → ℝ) (a l u : ℝ) (hlu : l ≤ u)
    (hbreak : ∀ i, y i ∉ Set.Ioo l u) :
    ∃ c d : ℝ, ∀ ρ ∈ Set.Icc l u, residual y a ρ = c*ρ+d := by
  classical
  let c : Fin N → ℝ := fun i => if u ≤ y i then -1 else 0
  let b : Fin N → ℝ := fun i => if u ≤ y i then y i else 0
  refine ⟨∑ i,c i,(∑ i,b i)-a,?_⟩
  intro ρ hρ
  have ht (i : Fin N) : max (y i-ρ) 0 = c i*ρ+b i := by
    by_cases hi : u ≤ y i
    · rw [max_eq_left (by linarith [hρ.2])]
      simp [c,b,hi]; ring
    · have hy : y i ≤ l := by
        by_contra hh
        exact hbreak i ⟨lt_of_not_ge hh,lt_of_not_ge hi⟩
      rw [max_eq_right (by linarith [hρ.1])]
      simp [c,b,hi]
  simp only [residual,ht,Finset.sum_add_distrib,← Finset.sum_mul]
  ring
lemma strictAnti {N : ℕ} (y : Fin N → ℝ) (a ymax : ℝ)
    (hm : IsGreatest (Set.range y) ymax) : StrictAntiOn (residual y a) (Set.Iic ymax) := by
  obtain ⟨j,hj⟩ := hm.1
  intro ρ hρ σ hσ hlt
  change ρ ≤ ymax at hρ
  change σ ≤ ymax at hσ
  apply sub_lt_sub_right
  apply Finset.sum_lt_sum
  · intro i _
    exact max_le_max (by linarith) le_rfl
  · refine ⟨j,Finset.mem_univ _,?_⟩
    rw [hj,max_eq_left (by linarith [hσ]),max_eq_left (by linarith [hσ])]
    linarith
lemma plateau {N : ℕ} (y : Fin N → ℝ) (a ymax : ℝ)
    (hm : IsGreatest (Set.range y) ymax) (ρ : ℝ) (hρ : ymax ≤ ρ) : residual y a ρ = -a := by
  have hz (i : Fin N) : max (y i-ρ) 0 = 0 := by
    apply max_eq_right
    have h := hm.2 (Set.mem_range_self i)
    linarith
  simp [residual,hz]
end CondatRoot

open scoped BigOperators
namespace CondatRoot
variable {N : ℕ} (y : Fin N → ℝ) (a : ℝ) (ha : 0 < a) (hN : 1 ≤ N)
    (ymax ymin : ℝ) (hmax : IsGreatest (Set.range y) ymax) (hmin : IsLeast (Set.range y) ymin)
include ha hN hmax hmin in
lemma initial_bounds :
    0 ≤ residual y a (ymin-a/N) ∧ residual y a (ymax-a/N) ≤ 0 ∧
    0 ≤ residual y a (ymax-a) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hc : 0 ≤ a/(N:ℝ) := div_nonneg ha.le hn.le
  have hcancel : (N:ℝ)*(a/(N:ℝ)) = a := by field_simp
  have hlo : a ≤ ∑ i, max (y i-(ymin-a/N)) 0 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      show a/(N:ℝ) ≤ max (y i-(ymin-a/N)) 0 from
        (by have hi := hmin.2 (Set.mem_range_self i); exact le_trans (by linarith) (le_max_left _ _)))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hcancel] using h
  have hhi : (∑ i, max (y i-(ymax-a/N)) 0) ≤ a := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      show max (y i-(ymax-a/N)) 0 ≤ a/(N:ℝ) from
        max_le (by have hi := hmax.2 (Set.mem_range_self i); linarith) hc)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hcancel] using h
  obtain ⟨j,hj⟩ := hmax.1
  have hsingle := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    show 0 ≤ max (y i-(ymax-a)) 0 from le_max_right _ _) (Finset.mem_univ j)
  have he : max (y j-(ymax-a)) 0 = a := by rw [hj]; simp [ha.le]
  rw [he] at hsingle
  unfold residual
  exact ⟨sub_nonneg.mpr hlo,sub_nonpos.mpr hhi,sub_nonneg.mpr hsingle⟩
end CondatRoot

open SimplexProj.Condat
open scoped BigOperators in
theorem solution (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a y x)
    (τ : ℝ) (hτ : ∀ n, x n = max (y n - τ) 0)
    (f : ℝ → ℝ) (hf : ∀ ρ, f ρ = ∑ n, max (y n - ρ) 0 - a)
    (ymax ymin : ℝ) (hmax : IsGreatest (Set.range y) ymax) (hmin : IsLeast (Set.range y) ymin) :
    f τ = 0 ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ ρ₁ ρ₂ : ℝ, ρ₁ ≤ ρ₂ → (∀ n, y n ∉ Set.Ioo ρ₁ ρ₂) →
      ∃ c d : ℝ, ∀ ρ ∈ Set.Icc ρ₁ ρ₂, f ρ = c * ρ + d) ∧
    StrictAntiOn f (Set.Iic ymax) ∧
    (∀ ρ ∈ Set.Ici ymax, f ρ = -a) ∧
    (∀ ρ : ℝ, f ρ < 0 → τ < ρ) ∧
    (∀ ρ : ℝ, 0 < f ρ → ρ < τ) ∧
    0 ≤ f (ymin - a / N) ∧ f (ymax - a / N) ≤ 0 ∧ 0 ≤ f (ymax - a) ∧
    max (ymax - a) (ymin - a / N) ≤ τ ∧ τ ≤ ymax - a / N := by
  have he : f = CondatRoot.residual y a := funext hf
  subst f
  let f := CondatRoot.residual y a
  have hz : f τ = 0 := by
    dsimp [f,CondatRoot.residual]
    simp_rw [← hτ]
    rw [hx.1.1,sub_self]
  have hm := CondatRoot.antitone y a
  have hs := CondatRoot.strictAnti y a ymax hmax
  have hp := CondatRoot.plateau y a ymax hmax
  have htmax : τ < ymax := by
    by_contra h
    have ht := hp τ (le_of_not_gt h)
    change f τ = -a at ht
    linarith
  have hneg (ρ : ℝ) (h : f ρ < 0) : τ < ρ := by
    by_contra hh
    have hc := hm (le_of_not_gt hh)
    change f τ ≤ f ρ at hc
    linarith
  have hpos (ρ : ℝ) (h : 0 < f ρ) : ρ < τ := by
    by_contra hh
    have hc := hm (le_of_not_gt hh)
    change f ρ ≤ f τ at hc
    linarith
  have hlow (ρ : ℝ) (h : 0 ≤ f ρ) : ρ ≤ τ := by
    have hrmax : ρ < ymax := by
      by_contra hh
      have hc := hp ρ (le_of_not_gt hh)
      change f ρ = -a at hc
      linarith
    by_contra hh
    have hc := hs htmax.le hrmax.le (lt_of_not_ge hh)
    change f ρ < f τ at hc
    linarith
  have hhigh (ρ : ℝ) (h : f ρ ≤ 0) : τ ≤ ρ := by
    by_contra hh
    have hr : ρ < τ := lt_of_not_ge hh
    have hc := hs (hr.trans htmax).le htmax.le hr
    change f τ < f ρ at hc
    linarith
  obtain ⟨hlo,hhi,hlomax⟩ := CondatRoot.initial_bounds y a ha hN ymax ymin hmax hmin
  exact ⟨hz,CondatRoot.convex y a,CondatRoot.affine_interval y a,hs,hp,hneg,hpos,
    hlo,hhi,hlomax,max_le (hlow _ hlomax) (hlow _ hlo),hhigh _ hhi⟩
#print axioms solution
