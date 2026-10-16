-- Prove2me | solution 1 for PooledRationing.AsymFeas.minimax_display
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:10:41.92371+00:00
-- url     : https://prove2.me/submissions/1fbd0a20-7c26-4953-9c80-93879b7cac85

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

set_option autoImplicit false
open PooledRationing.AsymFeas MeasureTheory

namespace PooledResearch

def mixPolicy {n m : ℕ} {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (lam mu : RandPolicy P c) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : RandPolicy P c where
  k := lam.k + mu.k
  wt := Fin.addCases (fun i => a * lam.wt i) (fun j => b * mu.wt j)
  pol := Fin.addCases lam.pol mu.pol
  wt_nonneg := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j; simpa only [Fin.addCases_left] using mul_nonneg ha (lam.wt_nonneg j)
    · intro j; simpa only [Fin.addCases_right] using mul_nonneg hb (mu.wt_nonneg j)
  wt_sum := by
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [← Finset.mul_sum, ← Finset.mul_sum, lam.wt_sum, mu.wt_sum]
    simpa only [mul_one] using hab

theorem service_mix {n m : ℕ} (F : Measure (Fin n → ℝ))
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (R : Fin n → ℝ → ℝ → ℝ) (lam mu : RandPolicy P c) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (j : Fin n) :
    service F R (mixPolicy lam mu a b ha hb hab) j =
      a * service F R lam j + b * service F R mu j := by
  change (∑ i : Fin (lam.k+mu.k),
    Fin.addCases (fun i => a*lam.wt i) (fun i => b*mu.wt i) i *
      detService F R (Fin.addCases lam.pol mu.pol i) j) = _
  rw [Fin.sum_univ_add]
  simp [service, Finset.mul_sum, mul_assoc]

theorem convex_service_range {n m : ℕ} (F : Measure (Fin n → ℝ))
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) :
    Convex ℝ (Set.range (fun lam : RandPolicy P c => service F R lam)) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨lam,rfl⟩
  rcases hy with ⟨mu,rfl⟩
  refine ⟨mixPolicy lam mu a b ha hb hab, ?_⟩
  funext j
  exact service_mix F R lam mu a b ha hb hab j

end PooledResearch

#print axioms PooledResearch.convex_service_range

set_option autoImplicit false
open scoped BigOperators

namespace PooledResearch

theorem approximate_domination {n : ℕ} (S : Set (Fin n → ℝ))
    (hne : S.Nonempty) (hconv : Convex ℝ S) (hbounded : Bornology.IsBounded S)
    (β : Fin n → ℝ)
    (hdual : ∀ w : Fin n → ℝ, 0 ≤ w → ∃ x ∈ S, ∑ j, w j * (β j - x j) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ x ∈ S, ∀ j, β j - ε ≤ x j := by
  classical
  let W : Set (Fin n → ℝ) := {w | 0 ≤ w ∧ (∑ j, w j) ≤ 1}
  let f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun x w => ∑ j, w j*(β j-x j)
  have hWne : W.Nonempty := ⟨0,by simp [W]⟩
  have hWclosed : IsClosed W := by
    change IsClosed (Set.Ici (0 : Fin n → ℝ) ∩ {w : Fin n → ℝ | (∑ j, w j) ≤ 1})
    exact isClosed_Ici.inter (isClosed_le (by fun_prop) continuous_const)
  have hWcompact : IsCompact W := by
    apply isCompact_Icc.of_isClosed_subset hWclosed
    intro w hw
    refine ⟨hw.1,?_⟩
    intro j
    exact (Finset.single_le_sum (fun i _ => hw.1 i) (Finset.mem_univ j)).trans hw.2
  have hWconv : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    constructor
    · intro j
      change 0 ≤ a*x j+b*y j
      exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
    · change (∑ j, (a*x j+b*y j)) ≤ 1
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      have hh := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      simpa only [mul_one,hab] using hh
  have hfx (x : Fin n → ℝ) : Continuous (f x) := by dsimp [f]; fun_prop
  have hfy (w : Fin n → ℝ) : Continuous (fun x => f x w) := by dsimp [f]; fun_prop
  have hfc (w : Fin n → ℝ) : ConvexOn ℝ (closure S) (fun x => f x w) := by
    refine ⟨hconv.closure,?_⟩
    intro x hx y hy a b ha hb hab
    apply le_of_eq
    dsimp [f]
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    nlinarith only [congrArg (fun t : ℝ => t*(w j*β j)) hab]
  have hfd (x : Fin n → ℝ) : ConcaveOn ℝ W (f x) := by
    refine ⟨hWconv,?_⟩
    intro w hw z hz a b ha hb hab
    apply le_of_eq
    dsimp [f]
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨x,hx,w,hw,hsaddle⟩ := Sion.exists_isSaddlePointOn
    hne.closure hconv.closure hbounded.isCompact_closure
    (fun w _ => (hfy w).continuousOn.lowerSemicontinuousOn)
    (fun w _ => (hfc w).quasiconvexOn)
    hWconv hWne hWcompact
    (fun x _ => (hfx x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hfd x).quasiconcaveOn)
  obtain ⟨y,hy,hyval⟩ := hdual w hw.1
  have hvalue (z) (hz : z ∈ W) : f x z ≤ 0 :=
    (hsaddle y (subset_closure hy) z hz).trans hyval
  have hdom (j : Fin n) : β j ≤ x j := by
    have hj : Pi.single j (1 : ℝ) ∈ W := by
      constructor
      · intro i; by_cases he : i=j <;> simp [he]
      · simp
    have hh := hvalue (Pi.single j 1) hj
    dsimp [f] at hh
    simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hh
    linarith
  obtain ⟨z,hz,hzx⟩ := Metric.mem_closure_iff.mp hx ε hε
  refine ⟨z,hz,?_⟩
  intro j
  have hj := norm_le_pi_norm (x-z) j
  rw [dist_eq_norm] at hzx
  have hnorm : |x j-z j| < ε := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hj.trans_lt hzx
  have hh := (abs_lt.mp hnorm).2
  linarith [hdom j]

end PooledResearch
#print axioms PooledResearch.approximate_domination

namespace PooledResearch

def purePolicy {n m : ℕ} {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (φ : DetPolicy P c) : RandPolicy P c where
  k := 1
  wt := fun _ => 1
  pol := fun _ => φ
  wt_nonneg := fun _ => by norm_num
  wt_sum := by simp

theorem service_pure {n m : ℕ} (F : Measure (Fin n → ℝ))
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (R : Fin n → ℝ → ℝ → ℝ) (φ : DetPolicy P c) (j : Fin n) :
    service F R (purePolicy φ) j = detService F R φ j := by
  change (∑ _i : Fin 1, (1 : ℝ) * detService F R φ j) = detService F R φ j
  simp

end PooledResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Jiang, Wang and Zhang, SSRN 3385089, the minimax step (20)–(21).
theorem solution {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (_hc : 0 ≤ c) (_hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (_hF2 : MemLp id 2 F) (_hDnn : ∀ᵐ D ∂F, (0 : Fin n → ℝ) ≤ D)
    (_hA1_mono : ∀ j d, Monotone (fun s => R j s d))
    (_hA1_usc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (_hA1_compact : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (h : (Fin n → ℝ) → ℝ) (hh : Integrable h F)
    (hRenv : ∀ D, ∀ x ∈ P c D, ∀ j, R j (x.1 j) (D j) ≤ h D)
    (hsel : ∀ w : Fin n → ℝ, 0 ≤ w → ∃ φ : DetPolicy P c,
      ∀ D, IsMaxOn (weightedService R w D) (P c D) (φ.toFun D))
    (h18 : ∀ w : Fin n → ℝ, 0 ≤ w →
      ∑ j, w j * β j ≤ ∫ D, maxWeightedValue P c R w D ∂F) :
    ∀ ε : ℝ, 0 < ε → ∃ lam : RandPolicy P c,
      ∀ w : Fin n → ℝ, 0 ≤ w → (∑ j, w j) ≤ 1 →
        ∑ j, w j * (β j - service F R lam j) ≤ ε := by
  classical
  have hrc (φ : DetPolicy P c) (j : Fin n) :
      Integrable (fun D => R j ((φ.toFun D).1 j) (D j)) F := by
    have hm : Measurable (fun D => R j ((φ.toFun D).1 j) (D j)) :=
      (hRmeas j).comp (((measurable_pi_apply j).comp φ.measurable'.fst).prodMk (measurable_pi_apply j))
    exact hh.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun D => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg _ _ _)]
      exact hRenv D (φ.toFun D) (φ.mem' D) j))
  have hdet (φ : DetPolicy P c) (j : Fin n) :
      0 ≤ detService F R φ j ∧ detService F R φ j ≤ ∫ D, h D ∂F := by
    constructor
    · exact integral_nonneg (fun D => hRnonneg _ _ _)
    · exact integral_mono (hrc φ j) hh (fun D => hRenv D (φ.toFun D) (φ.mem' D) j)
  let S := Set.range (fun lam : RandPolicy P c => service F R lam)
  obtain ⟨φ0,_⟩ := hsel 0 le_rfl
  have hne : S.Nonempty := ⟨_, Set.mem_range_self (PooledResearch.purePolicy φ0)⟩
  have hbdd : Bornology.IsBounded S := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|∫ D, h D ∂F|,?_⟩
    rintro x ⟨lam,rfl⟩
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
    intro j
    have hn : 0 ≤ service F R lam j :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (lam.wt_nonneg i) (hdet (lam.pol i) j).1)
    have hu : service F R lam j ≤ ∫ D, h D ∂F := by
      calc
        _ ≤ ∑ i, lam.wt i * (∫ D, h D ∂F) := Finset.sum_le_sum
          (fun i _ => mul_le_mul_of_nonneg_left (hdet (lam.pol i) j).2 (lam.wt_nonneg i))
        _ = _ := by rw [←Finset.sum_mul,lam.wt_sum,one_mul]
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    exact hu.trans (le_abs_self _)
  have hdual (w : Fin n → ℝ) (hw : 0 ≤ w) : ∃ x ∈ S, ∑ j, w j*(β j-x j) ≤ 0 := by
    obtain ⟨φ,hφ⟩ := hsel w hw
    have hm (D) : maxWeightedValue P c R w D = weightedService R w D (φ.toFun D) := by
      unfold maxWeightedValue
      apply IsGreatest.csSup_eq
      refine ⟨⟨φ.toFun D,φ.mem' D,rfl⟩,?_⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hφ D hx
    have hi : (∫ D, maxWeightedValue P c R w D ∂F) = ∑ j, w j * detService F R φ j := by
      simp_rw [hm]
      unfold weightedService
      rw [integral_finsetSum _ (fun j _ => (hrc φ j).const_mul (w j))]
      simp only [integral_const_mul,detService]
    refine ⟨service F R (PooledResearch.purePolicy φ),Set.mem_range_self _,?_⟩
    simp only [PooledResearch.service_pure,mul_sub,Finset.sum_sub_distrib]
    have hh := h18 w hw
    rw [hi] at hh
    linarith
  intro ε hε
  obtain ⟨x,⟨lam,rfl⟩,hx⟩ := PooledResearch.approximate_domination S hne
    (PooledResearch.convex_service_range F P c R) hbdd β hdual ε hε
  refine ⟨lam,?_⟩
  intro w hw hs
  calc
    _ ≤ ∑ j, w j*ε := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith [hx j]) (hw j))
    _ = (∑ j, w j)*ε := (Finset.sum_mul ..).symm
    _ ≤ ε := by nlinarith only [mul_le_mul_of_nonneg_right hs hε.le]

#print axioms solution
