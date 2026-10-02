-- Prove2me | solution 1 for Transcendence.coord_hermite_step
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:49:34.807503+00:00
-- url     : https://prove2.me/submissions/901f3878-28b2-4681-a47c-b8cecabbe947

import Mathlib
import Theorems.Thm_Transcendence_hermite_division_bound
import Theorems.Thm_Transcendence_hermite_basis
import Theorems.Thm_Transcendence_partials_eq_iteratedFDeriv

/-!
# One telescoping step of Schwarz's lemma for Cartesian products (Waldschmidt, DALAG Prop. 4.7)

Fix the coordinate `i`, the nodes `E` and the multiplicity `S₀`, and let `b` be the Hermite basis
of `Transcendence.hermite_basis`. With `pd i g z` the derivative of the slice `w ↦ g (update z i w)`
at `z i`, the step replaces `g` by
`T z = ∑_{ζ ∈ E, k < S₀} (pd i)^[k] g (update z i ζ) · b_{ζ,k}(z i)`.

1. **Bounds.** For each `z`, `T z = ρ(z i)`, where `ρ` is the Hermite remainder of the slice
   through `z` at the nodes `S₀ • E` (`Transcendence.hermite_division_bound`): `ρ` has the jets of
   the slice, which are values of `(pd i)^[k] g`, so `ρ` is `T` in the basis `b`. The division and
   its bounds give both estimates.
2. **Smoothness.** Iterated slice derivatives along a list of coordinates are values of
   `iteratedFDeriv` (`Transcendence.partials_eq_iteratedFDeriv`), hence smooth; so is `T`, and it
   is analytic.
3. **Vanishing.** `pd j` with `j ≠ i` passes through the frozen coordinate `i` and the factor
   `b_{ζ,k}(z i)`, so a derivative of `T` along `v` (avoiding `i`) is a combination of derivatives
   of `g` along `v` followed by `k` times `i`, at the points `update ξ i ζ`.
-/

namespace CoordHermiteStep

open Polynomial Metric Function
open scoped ContDiff

variable {ι : Type*} [DecidableEq ι]

/-! ## 1. Slices and partial derivatives -/

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

/-- Iterated partial derivatives along a list of coordinates (the last one is applied first). -/
noncomputable def pdList (L : List ι) (g : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  L.foldr pd g

lemma pdList_cons (j : ι) (L : List ι) (g : (ι → ℂ) → ℂ) :
    pdList (j :: L) g = pd j (pdList L g) := rfl

lemma pdList_append (L M : List ι) (g : (ι → ℂ) → ℂ) :
    pdList (L ++ M) g = pdList L (pdList M g) := List.foldr_append

lemma pdList_replicate (k : ℕ) (i : ι) (g : (ι → ℂ) → ℂ) :
    pdList (List.replicate k i) g = (pd i)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, pdList_cons, ih, Function.iterate_succ_apply']

variable [Fintype ι]

/-- Mixed partials along `List.ofFn L` are values of `iteratedFDeriv` on coordinate vectors. -/
lemma pdList_ofFn {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) {k : ℕ} (L : Fin k → ι) (z : ι → ℂ) :
    pdList (List.ofFn L) g z = iteratedFDeriv ℂ k g z (fun l => Pi.single (L l) 1) :=
  Transcendence.partials_eq_iteratedFDeriv L (hg.of_le le_top) z

lemma contDiff_pdList (L : List ι) {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) :
    ContDiff ℂ ω (pdList L g) := by
  rw [← List.ofFn_get L, funext (pdList_ofFn hg L.get)]
  exact (ContinuousMultilinearMap.apply ℂ _ ℂ _).contDiff.comp (hg.iteratedFDeriv_right (by simp))

lemma contDiff_iterate_pd {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) (i : ι) (k : ℕ) :
    ContDiff ℂ ω ((pd i)^[k] g) :=
  pdList_replicate k i g ▸ contDiff_pdList _ hg

lemma contDiff_update_const (i : ι) (c : ℂ) :
    ContDiff ℂ ω (fun z : ι → ℂ => update z i c) := by
  rw [contDiff_pi]
  intro j
  by_cases h : j = i
  · subst h
    simpa using contDiff_const
  · simpa [update_of_ne h] using contDiff_apply ℂ ℂ j

lemma differentiable_slice {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) (z : ι → ℂ) (i : ι) :
    Differentiable ℂ (fun w => g (update z i w)) :=
  (hg.comp (contDiff_update ω z i)).differentiable (by simp)

/-! ## 2. The step and its bounds -/

/-- The step in coordinate `i`: the slice through `z` is replaced by its Hermite interpolant at the
nodes `E` (multiplicity `S₀`), written in the basis `b` and evaluated at `z i`. -/
noncomputable def T {E : Finset ℂ} {S₀ : ℕ} (b : ↥E × Fin S₀ → ℂ[X]) (i : ι) (g : (ι → ℂ) → ℂ)
    (z : ι → ℂ) : ℂ :=
  ∑ x : ↥E × Fin S₀, (pd i)^[x.2] g (update z i x.1) * (b x).eval (z i)

lemma contDiff_T {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) {E : Finset ℂ} {S₀ : ℕ}
    (b : ↥E × Fin S₀ → ℂ[X]) (i : ι) : ContDiff ℂ ω (T b i g) := by
  unfold T
  refine ContDiff.sum fun x _ => ?_
  exact ((contDiff_iterate_pd hg i x.2).comp (contDiff_update_const i x.1)).mul
    ((Polynomial.differentiable _).contDiff.comp (contDiff_apply ℂ ℂ i))

/-- One slice, through `z` in the `R`-polydisc: `g z = T z + P · c` with
`P = ∏_{ζ ∈ E} (z i - ζ)^S₀`, `2|T z| + K ≤ 3^p K` and `|c| ≤ (3/R)^p K`, where
`p = card E * S₀`. -/
lemma slice_step {g : (ι → ℂ) → ℂ} (hg : ContDiff ℂ ω g) (i : ι) {E : Finset ℂ} {S₀ : ℕ}
    {b : ↥E × Fin S₀ → ℂ[X]} (hb : ∀ q ∈ degreeLT ℂ (E.card * S₀),
      q = ∑ x : ↥E × Fin S₀, C ((derivative^[x.2] q).eval (x.1 : ℂ)) * b x)
    {r R K : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) (hE : ∀ ζ ∈ E, ‖ζ‖ ≤ r)
    (hK : ∀ y ∈ closedBall (0 : ι → ℂ) R, ‖g y‖ ≤ K) {z : ι → ℂ} (hz : ‖z‖ ≤ R) :
    ∃ c : ℂ, g z = T b i g z + (∏ ζ ∈ E, (z i - ζ) ^ S₀) * c ∧
      2 * ‖T b i g z‖ + K ≤ 3 ^ (E.card * S₀) * K ∧ ‖c‖ ≤ (3 / R) ^ (E.card * S₀) * K := by
  have hM : ∀ w ∈ closedBall (0 : ℂ) R, ‖g (update z i w)‖ ≤ K := by
    intro w hw
    refine hK _ (mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (by linarith)).mpr
      fun j => ?_))
    by_cases h : j = i
    · subst h
      simpa using mem_closedBall_zero_iff.mp hw
    · rw [update_of_ne h]
      exact (norm_le_pi_norm z j).trans hz
  obtain ⟨ρ, q, hρ, -, hdiv, hjet, hbd⟩ := Transcendence.hermite_division_bound hr hR (S₀ • E.val)
    (fun ζ h => hE ζ (Multiset.mem_nsmul.mp h).2) (differentiable_slice hg z i) hM
  have hcard : Multiset.card (S₀ • E.val) = E.card * S₀ := by
    rw [Multiset.card_nsmul, Finset.card_val, mul_comm]
  rw [hcard] at hρ hbd
  have hT : T b i g z = ρ.eval (z i) := by
    rw [T, hb ρ hρ, eval_finsetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [eval_mul, eval_C, hjet x.1 x.2 ?_, iteratedDeriv_slice]
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem E.nodup x.1.2, mul_one]
    exact x.2.2
  obtain ⟨h1, h2⟩ := hbd (z i) (mem_closedBall_zero_iff.mpr ((norm_le_pi_norm z i).trans hz))
  refine ⟨q (z i), ?_, hT ▸ h1, h2⟩
  have h := hdiv (z i)
  simp only [update_eq_self] at h
  rwa [Multiset.map_nsmul, Multiset.prod_nsmul, ← Finset.prod_eq_multiset_prod, ← Finset.prod_pow,
    ← hT] at h

/-! ## 3. Partial derivatives in the other coordinates pass through the step -/

/-- `pd j` (for `j ≠ i`) passes through freezing coordinate `i` and multiplying by a
polynomial in `z i`. -/
lemma pd_freeze {α : Type*} (s : Finset α) (h : α → (ι → ℂ) → ℂ)
    (hh : ∀ x, ContDiff ℂ ω (h x)) (c : α → ℂ) (φ : α → ℂ[X]) {i j : ι} (hji : j ≠ i) :
    pd j (fun z => ∑ x ∈ s, h x (update z i (c x)) * (φ x).eval (z i)) =
      fun z => ∑ x ∈ s, pd j (h x) (update z i (c x)) * (φ x).eval (z i) := by
  funext z
  simp only [pd]
  have e : (fun w => ∑ x ∈ s, h x (update (update z j w) i (c x)) *
      (φ x).eval (update z j w i)) =
      fun w => ∑ x ∈ s, h x (update (update z i (c x)) j w) * (φ x).eval (z i) := by
    funext w
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [update_comm hji, update_of_ne hji.symm]
  rw [e, deriv_fun_sum fun x _ =>
    ((differentiable_slice (hh x) _ j).mul_const _).differentiableAt]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [deriv_mul_const (differentiable_slice (hh x) _ j).differentiableAt, update_of_ne hji]

lemma pdList_freeze {α : Type*} (s : Finset α) (h : α → (ι → ℂ) → ℂ)
    (hh : ∀ x, ContDiff ℂ ω (h x)) (c : α → ℂ) (φ : α → ℂ[X]) {i : ι} :
    ∀ (L : List ι), (∀ j ∈ L, j ≠ i) →
      pdList L (fun z => ∑ x ∈ s, h x (update z i (c x)) * (φ x).eval (z i)) =
        fun z => ∑ x ∈ s, pdList L (h x) (update z i (c x)) * (φ x).eval (z i)
  | [], _ => rfl
  | j :: L, hL => by
    rw [pdList_cons, pdList_freeze s h hh c φ L fun j' hj' => hL j' (List.mem_cons_of_mem _ hj')]
    exact pd_freeze s (fun x => pdList L (h x)) (fun x => contDiff_pdList L (hh x)) c φ
      (hL j List.mem_cons_self)

end CoordHermiteStep

open Polynomial Metric Function CoordHermiteStep in
open scoped ContDiff in
/-- **One step of Schwarz's lemma for Cartesian products** (Waldschmidt, DALAG, proof of
Prop. 4.7). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) (i : ι) (E : Finset ℂ) (S₀ : ℕ)
    {r R K : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) (hE : ∀ ζ ∈ E, ‖ζ‖ ≤ r)
    (hK : ∀ y ∈ Metric.closedBall (0 : ι → ℂ) R, ‖g y‖ ≤ K) :
    ∃ h : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ h Set.univ ∧
      (∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖h z‖ ≤ 3 ^ (E.card * S₀) * K) ∧
      (∀ z ∈ Metric.closedBall (0 : ι → ℂ) r,
        ‖g z - h z‖ ≤ (2 * r) ^ (E.card * S₀) * ((3 / R) ^ (E.card * S₀) * K)) ∧
      ∀ (m : ℕ) (v : Fin m → ι), (∀ t, v t ≠ i) → ∀ ξ : ι → ℂ,
        (∀ ζ ∈ E, ∀ k < S₀, iteratedFDeriv ℂ (m + k) g (Function.update ξ i ζ)
          (fun t => Pi.single (Fin.append v (fun _ : Fin k => i) t) 1) = 0) →
        iteratedFDeriv ℂ m h ξ (fun t => Pi.single (v t) 1) = 0 := by
  have hgC : ContDiff ℂ ω g := hg.contDiff
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp; linarith))
  obtain ⟨b, -, -, hb⟩ := Transcendence.hermite_basis E S₀
  refine ⟨T b i g, (contDiff_T hgC b i).analyticOnNhd, fun z hz => ?_, fun z hz => ?_, ?_⟩
  · obtain ⟨-, -, h1, -⟩ := slice_step hgC i hb hr hR hE hK (mem_closedBall_zero_iff.mp hz)
    linarith [norm_nonneg (T b i g z)]
  · have hz' : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
    obtain ⟨c, hc, -, h2⟩ := slice_step hgC i hb hr hR hE hK (by linarith)
    rw [hc, add_sub_cancel_left, norm_mul]
    refine mul_le_mul ?_ h2 (norm_nonneg _) (by positivity)
    rw [norm_prod, mul_comm E.card S₀, pow_mul, ← Finset.prod_const]
    gcongr with ζ hζ
    rw [norm_pow]
    gcongr
    calc ‖z i - ζ‖ ≤ ‖z i‖ + ‖ζ‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith [hE ζ hζ, norm_le_pi_norm z i]
  · intro m v hv ξ hvan
    have hT : T b i g = fun z => ∑ x : ↥E × Fin S₀,
        (pd i)^[x.2] g (update z i x.1) * (b x).eval (z i) := rfl
    rw [← pdList_ofFn (contDiff_T hgC b i) v ξ, hT,
      pdList_freeze Finset.univ (fun x : ↥E × Fin S₀ => (pd i)^[x.2] g)
        (fun x => contDiff_iterate_pd hgC i x.2) (fun x => (x.1 : ℂ)) b (List.ofFn v)
        fun j hj => by obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hj; exact hv t]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← pdList_replicate, ← pdList_append, ← List.ofFn_const, ← List.ofFn_fin_append,
      pdList_ofFn hgC, hvan x.1 x.1.2 x.2 x.2.2, zero_mul]
