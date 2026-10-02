-- Prove2me | solution 1 for Transcendence.polydisc_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:26:30.396017+00:00
-- url     : https://prove2.me/submissions/bba03203-eeb3-479a-b1f2-d03e6f0448c6

import Mathlib
import Theorems.Thm_Transcendence_partials_eq_iteratedFDeriv

/-!
# Cauchy's inequalities on a polydisc (Waldschmidt, DALAG p. XVII)

For `F` entire on `ι → ℂ` with `‖F‖ ≤ M` on the closed polydisc `closedBall p ρ` (sup norm), the
mixed partial derivative at `p` along the coordinate directions `L 0, …, L (k-1)` is at most
`σ! · M / ρ^k`, where `σ_ν = #{l | L l = ν}` and `σ! = ∏ σ_ν!`.

1. **Slices.** `pd i g z` is the derivative of the slice `w ↦ g (update z i w)`; derivatives of
   slices are slices of `pd`.
2. **Lists of directions.** `pdList s g` applies `pd` along the list `s`; on `List.ofFn L` it is
   `iteratedFDeriv ℂ k g` on the vectors `Pi.single (L l) 1`
   (`Transcendence.partials_eq_iteratedFDeriv`), hence smooth for smooth `g`. Partial derivatives
   commute (symmetry of `iteratedFDeriv`), so `pdList s g` only depends on `s` up to permutation,
   and `L` may be sorted into blocks `ν₁^{σ₁} ⋯ ν_m^{σ_m}` of distinct coordinates.
3. **Iterated one-variable Cauchy.** The estimate on the circle of radius `ρ` in coordinate `ν₁`
   reduces the first block to the remaining ones, at points whose coordinates `ν₂, …, ν_m` are
   still those of `p`. These points lie in the polydisc, so induction on the blocks applies.
-/

namespace PolydiscCauchy

open Metric Function
open scoped ContDiff

variable {ι : Type*} [DecidableEq ι]

/-! ## 1. Slices, lists of directions and blocks -/

/-- Partial derivative in coordinate `i`, taken on the slice through `z`. -/
noncomputable def pd (i : ι) (g : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  deriv (fun w => g (update z i w)) (z i)

/-- Derivatives of a slice are slices of iterated partial derivatives (no regularity needed). -/
lemma iteratedDeriv_slice (g : (ι → ℂ) → ℂ) (i : ι) (z : ι → ℂ) (k : ℕ) :
    iteratedDeriv k (fun w => g (update z i w)) = fun w => (pd i)^[k] g (update z i w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    simp only [Function.iterate_succ_apply', pd, update_idem, update_self]

lemma iterate_pd_eq (g : (ι → ℂ) → ℂ) (i : ι) (z : ι → ℂ) (k : ℕ) :
    (pd i)^[k] g z = iteratedDeriv k (fun w => g (update z i w)) (z i) := by
  simp only [iteratedDeriv_slice, update_eq_self]

/-- Iterated partial derivatives along a list of coordinates (the last one is applied first). -/
noncomputable def pdList (s : List ι) (g : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  s.foldr pd g

lemma pdList_cons (j : ι) (s : List ι) (g : (ι → ℂ) → ℂ) :
    pdList (j :: s) g = pd j (pdList s g) := rfl

lemma pdList_append (s t : List ι) (g : (ι → ℂ) → ℂ) :
    pdList (s ++ t) g = pdList s (pdList t g) := List.foldr_append

lemma pdList_replicate (k : ℕ) (i : ι) (g : (ι → ℂ) → ℂ) :
    pdList (List.replicate k i) g = (pd i)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, pdList_cons, ih, Function.iterate_succ_apply']

/-- `blocks n [ν₁, …, ν_m] = ν₁^{n ν₁} ++ ⋯ ++ ν_m^{n ν_m}`. -/
def blocks (n : ι → ℕ) : List ι → List ι
  | [] => []
  | ν :: cs => List.replicate (n ν) ν ++ blocks n cs

lemma count_blocks (n : ι → ℕ) (a : ι) :
    ∀ cs : List ι, cs.Nodup → (blocks n cs).count a = if a ∈ cs then n a else 0
  | [], _ => by simp [blocks]
  | ν :: cs, hnd => by
    rw [blocks, List.count_append, count_blocks n a cs (List.nodup_cons.mp hnd).2,
      List.count_replicate]
    by_cases h : a = ν
    · subst h
      simp [(List.nodup_cons.mp hnd).1]
    · simp [h, Ne.symm h]

lemma count_ofFn {k : ℕ} (L : Fin k → ι) (a : ι) :
    (List.ofFn L).count a = (Finset.univ.filter fun l => L l = a).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    simp [add_comm]

/-! ## 2. Smooth functions: `pdList` is `iteratedFDeriv`, and is symmetric -/

variable [Fintype ι]

lemma differentiable_slice {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) (z : ι → ℂ) (i : ι) :
    Differentiable ℂ (fun w => g (update z i w)) :=
  (hg.comp (contDiff_update ω z i)).differentiable (by simp)

/-- Mixed partials along `List.ofFn L` are values of `iteratedFDeriv` on coordinate vectors. -/
lemma pdList_ofFn {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) {k : ℕ} (L : Fin k → ι) (z : ι → ℂ) :
    pdList (List.ofFn L) g z = iteratedFDeriv ℂ k g z (fun l => Pi.single (L l) 1) :=
  Transcendence.partials_eq_iteratedFDeriv L (hg.of_le le_top) z

lemma contDiff_pdList (s : List ι) {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) :
    ContDiff ℂ ω (pdList s g) := by
  rw [← List.ofFn_get s, funext (pdList_ofFn hg s.get)]
  exact (ContinuousMultilinearMap.apply ℂ _ ℂ _).contDiff.comp (hg.iteratedFDeriv_right (by simp))

/-- Partial derivatives commute (symmetry of the second derivative). -/
lemma pd_comm {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) (i j : ι) :
    pd i (pd j g) = pd j (pd i g) := by
  funext z
  have e : (fun l : Fin 2 => (Pi.single (![i, j] l) 1 : ι → ℂ)) ∘ Equiv.swap 0 1 =
      fun l => (Pi.single (![j, i] l) 1 : ι → ℂ) := by
    funext l
    fin_cases l <;> rfl
  have h := hg.contDiffAt.iteratedFDeriv_comp_perm (x := z)
    (fun l : Fin 2 => (Pi.single (![i, j] l) 1 : ι → ℂ)) (Equiv.swap 0 1)
  rw [e, ← pdList_ofFn hg, ← pdList_ofFn hg] at h
  exact h.symm

/-- `pdList s g` only depends on the list of directions `s` up to permutation. -/
lemma pdList_perm {s t : List ι} (h : s.Perm t) :
    ∀ {g : (ι → ℂ) → ℂ}, ContDiff ℂ ω g → pdList s g = pdList t g := by
  induction h with
  | nil => intro g _; rfl
  | cons x _ ih => intro g hg; rw [pdList_cons, pdList_cons, ih hg]
  | swap x y s => intro g hg; exact pd_comm (contDiff_pdList s hg) y x
  | trans _ _ ih₁ ih₂ => intro g hg; rw [ih₁ hg, ih₂ hg]

/-! ## 3. The iterated one-variable Cauchy estimate -/

/-- At a point `q` of the polydisc whose coordinates in `cs` are those of `p`, the mixed partial
along the blocks of `cs` is at most `∏_{ν ∈ cs} (n ν)! · M / ρ^order`. -/
lemma cauchy_blocks {G : (ι → ℂ) → ℂ} (hG : ContDiff ℂ ω G) {p : ι → ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ closedBall p ρ, ‖G z‖ ≤ M) (n : ι → ℕ) :
    ∀ cs : List ι, cs.Nodup → ∀ q ∈ closedBall p ρ, (∀ ν ∈ cs, q ν = p ν) →
      ‖pdList (blocks n cs) G q‖ ≤
        (cs.map fun ν => ((n ν).factorial : ℝ)).prod * M / ρ ^ (blocks n cs).length
  | [], _, q, hq, _ => by simpa [blocks, pdList] using hM q hq
  | ν :: cs, hnd, q, hq, hqp => by
    have hν : ν ∉ cs := (List.nodup_cons.mp hnd).1
    have ih := cauchy_blocks hG hρ hM n cs (List.nodup_cons.mp hnd).2
    have hH : ContDiff ℂ ω (pdList (blocks n cs) G) := contDiff_pdList _ hG
    rw [blocks, pdList_append, pdList_replicate, iterate_pd_eq, hqp ν (by simp)]
    refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n ν) hρ
      (differentiable_slice hH q ν).diffContOnCl
      (fun w hw => ih (update q ν w) ?_ ?_)).trans (le_of_eq ?_)
    · rw [mem_closedBall, dist_pi_le_iff hρ.le]
      intro j
      by_cases hj : j = ν
      · rw [hj, update_self]
        exact (mem_sphere.mp hw).le
      · rw [update_of_ne hj]
        exact (dist_le_pi_dist q p j).trans (mem_closedBall.mp hq)
    · intro ν' hν'
      rw [update_of_ne (fun h : ν' = ν => hν (h ▸ hν'))]
      exact hqp ν' (List.mem_cons_of_mem _ hν')
    · simp only [List.map_cons, List.prod_cons, List.length_append, List.length_replicate,
        pow_add]
      ring

/-! ## 4. Assembly -/

/-- The main estimate (same statement as `solution`). -/
theorem main {F : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) (p : ι → ℂ) {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : ∀ z ∈ Metric.closedBall p ρ, ‖F z‖ ≤ M) (k : ℕ) (L : Fin k → ι) :
    ‖iteratedFDeriv ℂ k F p (fun l => Pi.single (L l) 1)‖ ≤
      (∏ ν, ((Finset.univ.filter fun l => L l = ν).card.factorial : ℝ)) * M / ρ ^ k := by
  have hFC : ContDiff ℂ ω F := hF.contDiff
  set n : ι → ℕ := fun ν => (Finset.univ.filter fun l => L l = ν).card with hn
  set cs := (Finset.univ : Finset ι).toList
  have hperm : (List.ofFn L).Perm (blocks n cs) := by
    rw [List.perm_iff_count]
    intro a
    rw [count_ofFn, count_blocks n a cs (Finset.nodup_toList _)]
    simp [hn, cs]
  have hlen : (blocks n cs).length = k := by
    rw [← hperm.length_eq, List.length_ofFn]
  rw [← pdList_ofFn hFC L p, pdList_perm hperm hFC]
  have h := cauchy_blocks hFC hρ hM n cs (Finset.nodup_toList _) p (mem_closedBall_self hρ.le)
    (fun _ _ => rfl)
  rwa [hlen, Finset.prod_map_toList] at h

end PolydiscCauchy

/-- **Cauchy's inequalities on a polydisc** (Waldschmidt, DALAG p. XVII). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (p : ι → ℂ) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ Metric.closedBall p ρ, ‖F z‖ ≤ M) (k : ℕ) (L : Fin k → ι) :
    ‖iteratedFDeriv ℂ k F p (fun l => Pi.single (L l) 1)‖ ≤
      (∏ ν, ((Finset.univ.filter fun l => L l = ν).card.factorial : ℝ)) * M / ρ ^ k := by
  exact PolydiscCauchy.main hF p hρ hM k L
