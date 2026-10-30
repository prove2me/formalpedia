-- Prove2me | solution 1 for SideConstrainedDTA.Existence.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:56:49.066721+00:00
-- url     : https://prove2.me/submissions/f3213879-20bd-4e7a-8bf6-f8b3d0ffc5bd

import Mathlib
import Theorems.Thm_AGT_brouwer_fixed_point

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence.Sol34

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Metric projection onto a nonempty complete convex set: variational characterisation and
nonexpansiveness. -/
lemma exists_proj {K : Set H} (hne : K.Nonempty) (hc : IsComplete K) (hcv : Convex ℝ K) :
    ∃ P : H → H, (∀ x, P x ∈ K) ∧ (∀ x, ∀ w ∈ K, inner ℝ (x - P x) (w - P x) ≤ 0) ∧
      LipschitzWith 1 P := by
  choose P hPK hPn using fun x => exists_norm_eq_iInf_of_complete_convex hne hc hcv x
  have hvar : ∀ x, ∀ w ∈ K, inner ℝ (x - P x) (w - P x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hcv (hPK x)).1 (hPn x)
  refine ⟨P, hPK, hvar, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 := hvar x (P y) (hPK y)
  have h2 := hvar y (P x) (hPK x)
  have key : ‖P x - P y‖ ^ 2 ≤ inner ℝ (x - y) (P x - P y) := by
    have e : inner ℝ (x - y) (P x - P y) - ‖P x - P y‖ ^ 2 =
        -(inner ℝ (x - P x) (P y - P x)) - inner ℝ (y - P y) (P x - P y) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  have hcs := real_inner_le_norm (x - y) (P x - P y)
  rcases eq_or_lt_of_le (norm_nonneg (P x - P y)) with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- Bounded sequences in a separable Hilbert space have weakly convergent subsequences. -/
lemma weak_subseq [TopologicalSpace.SeparableSpace H] (x : ℕ → H) (R : ℝ)
    (hR : ∀ n, ‖x n‖ ≤ R) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ xs : H,
      ∀ g, Tendsto (fun n => inner ℝ (x (φ n)) g) atTop (𝓝 (inner ℝ xs g)) := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ H 0 R
    (x := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (x n))) (fun n => by
      simpa [mem_closedBall_zero_iff] using hR n)
  refine ⟨φ, hφ, (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual a), fun g => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact ((WeakDual.eval_continuous g).tendsto a).comp hlim

/-- Closed convex sets are weakly sequentially closed. -/
lemma weak_closed {C : Set H} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (x : ℕ → H) (hx : ∀ n, x n ∈ C) (xs : H)
    (hw : ∀ g, Tendsto (fun n => inner ℝ (x n) g) atTop (𝓝 (inner ℝ xs g))) : xs ∈ C := by
  obtain ⟨P, hPK, hvar, -⟩ := exists_proj hne hclosed.isComplete hconv
  have h1 : ∀ n, inner ℝ (x n) (xs - P xs) ≤ inner ℝ (P xs) (xs - P xs) := by
    intro n
    have := hvar xs (x n) (hx n)
    rw [real_inner_comm, inner_sub_left] at this
    linarith
  have h2 := le_of_tendsto' (hw (xs - P xs)) h1
  have h3 : inner ℝ (xs - P xs) (xs - P xs) ≤ 0 := by
    rw [inner_sub_left]; linarith
  rw [real_inner_self_eq_norm_sq] at h3
  have : xs - P xs = 0 := by
    have := sq_nonneg ‖xs - P xs‖
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (xs - P xs)])
  rw [sub_eq_zero.1 this]
  exact hPK xs

/-- Lions' theorem in a separable Hilbert space. -/
lemma lions [TopologicalSpace.SeparableSpace H] (C : Set H) (A : H → H) (hne : C.Nonempty)
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hbdd : Bornology.IsBounded C)
    (hA : ∀ (x : ℕ → H) (x₀ : H), (∀ n, x n ∈ C) → x₀ ∈ C →
      (∀ g, Tendsto (fun n => inner ℝ (x n) g) atTop (𝓝 (inner ℝ x₀ g))) →
      Tendsto (fun n => A (x n)) atTop (𝓝 (A x₀))) :
    ∃ h ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (A h) (y - h) := by
  classical
  -- strong continuity of A on C
  have hAC : ContinuousOn A C := by
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_iff_seqContinuous.2 fun u c hu => ?_
    have hu' : Tendsto (fun n => (u n : H)) atTop (𝓝 (c : H)) :=
      (continuous_subtype_val.tendsto c).comp hu
    exact hA (fun n => u n) c (fun n => (u n).2) c.2 fun g => hu'.inner tendsto_const_nhds
  -- finite-dimensional step
  have hfin : ∀ s : Finset H, (s : Set H) ⊆ C → (s : Set H).Nonempty →
      ∃ v ∈ convexHull ℝ (s : Set H), ∀ w ∈ convexHull ℝ (s : Set H),
        0 ≤ inner ℝ (A v) (w - v) := by
    intro s hsC hsne
    set K := convexHull ℝ (s : Set H) with hK
    have hKC : K ⊆ C := convexHull_min hsC hconv
    have hKcpt : IsCompact K := s.finite_toSet.isCompact_convexHull ℝ
    have hKcv : Convex ℝ K := convex_convexHull ℝ _
    have hKne : K.Nonempty := hsne.mono (subset_convexHull ℝ _)
    obtain ⟨P, hPK, hvar, hLip⟩ := exists_proj hKne hKcpt.isComplete hKcv
    set V := Submodule.span ℝ (s : Set H) with hV
    have hKV : K ⊆ V := convexHull_min Submodule.subset_span (Submodule.convex V)
    let K' : Set V := {v | (v : H) ∈ K}
    have hVcl : IsClosed (V : Set H) := Submodule.closed_of_finiteDimensional V
    have hK'cpt : IsCompact K' :=
      hVcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKcpt
    have hK'cv : Convex ℝ K' := hKcv.linear_preimage V.subtype
    obtain ⟨k0, hk0⟩ := hKne
    have hK'ne : K'.Nonempty := ⟨⟨k0, hKV hk0⟩, hk0⟩
    let g : V → H := fun v => P ((v : H) - A v)
    let f : V → V := fun v => ⟨g v, hKV (hPK _)⟩
    have hgc : ContinuousOn g K' := by
      have hA' : ContinuousOn (fun v : V => A v) K' :=
        hAC.comp continuous_subtype_val.continuousOn fun v hv => hKC hv
      exact hLip.continuous.comp_continuousOn
        (continuous_subtype_val.continuousOn.sub hA')
    have hfc : ContinuousOn f K' := by
      rw [continuousOn_iff_continuous_restrict] at hgc ⊢
      exact hgc.subtype_mk _
    have hfK : MapsTo f K' K' := fun v _ => hPK _
    obtain ⟨v, hvK, hfv⟩ := AGT.brouwer_fixed_point hK'cv hK'cpt hK'ne f hfc hfK
    have hPv : P ((v : H) - A v) = v := congrArg Subtype.val hfv
    refine ⟨v, hvK, fun w hw => ?_⟩
    have := hvar ((v : H) - A v) w hw
    rw [hPv] at this
    have e : (v : H) - A v - v = -A v := by abel
    rw [e, inner_neg_left] at this
    linarith
  -- dense sequence in C
  haveI : Nonempty C := hne.to_subtype
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq C
  let s : ℕ → Finset H := fun n => (Finset.range (n + 1)).image fun k => (y k : H)
  have hsC : ∀ n, (s n : Set H) ⊆ C := by
    intro n z hz
    simp only [s, Finset.coe_image, Finset.coe_range, mem_image] at hz
    obtain ⟨k, -, rfl⟩ := hz
    exact (y k).2
  have hsne : ∀ n, (s n : Set H).Nonempty := fun n =>
    ⟨(y 0 : H), by
      simp only [s, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
      exact ⟨0, by omega, rfl⟩⟩
  choose x hxK hxvi using fun n => hfin (s n) (hsC n) (hsne n)
  have hxC : ∀ n, x n ∈ C := fun n => convexHull_min (hsC n) hconv (hxK n)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
  obtain ⟨φ, hφ, xs, hw⟩ := weak_subseq x R fun n => hR _ (hxC n)
  have hxsC : xs ∈ C := weak_closed hne hclosed hconv (fun n => x (φ n)) (fun n => hxC _) xs hw
  have hAlim := hA (fun n => x (φ n)) xs (fun n => hxC _) hxsC hw
  -- strong × weak convergence
  have hsw : Tendsto (fun n => inner ℝ (A (x (φ n))) (x (φ n))) atTop
      (𝓝 (inner ℝ (A xs) xs)) := by
    have t1 : Tendsto (fun n => inner ℝ (A (x (φ n)) - A xs) (x (φ n))) atTop (𝓝 0) := by
      have hn : Tendsto (fun n => ‖A (x (φ n)) - A xs‖ * R) atTop (𝓝 0) := by
        have := (tendsto_iff_norm_sub_tendsto_zero.1 hAlim).mul_const R
        simpa using this
      refine squeeze_zero_norm (fun n => ?_) hn
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_left (hR _ (hxC _)) (norm_nonneg _)
    have t2 : Tendsto (fun n => inner ℝ (A xs) (x (φ n))) atTop (𝓝 (inner ℝ (A xs) xs)) := by
      simp_rw [real_inner_comm _ (A xs)]
      exact hw (A xs)
    have := t1.add t2
    simp only [zero_add] at this
    refine this.congr fun n => ?_
    rw [inner_sub_left]; ring
  have hk : ∀ k, 0 ≤ inner ℝ (A xs) ((y k : H) - xs) := by
    intro k
    have hlim : Tendsto (fun n => inner ℝ (A (x (φ n))) ((y k : H) - x (φ n))) atTop
        (𝓝 (inner ℝ (A xs) ((y k : H) - xs))) := by
      simp_rw [inner_sub_right]
      exact (hAlim.inner tendsto_const_nhds).sub hsw
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    refine hxvi (φ n) _ (subset_convexHull ℝ _ ?_)
    simp only [s, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
    exact ⟨k, by have := hφ.id_le n; simp only [id] at this; omega, rfl⟩
  refine ⟨xs, hxsC, fun z hz => ?_⟩
  have := hy.induction_on (p := fun b : C => 0 ≤ inner ℝ (A xs) ((b : H) - xs)) ⟨z, hz⟩
    (isClosed_le continuous_const
      ((continuous_const.inner (continuous_subtype_val.sub continuous_const)))) hk
  exact this

end SideConstrainedDTA.Existence.Sol34

theorem solution (a b : ℝ) (d : ℕ)
    (C : Set (PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b)))))
    (A : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))) →
      PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))))
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hbdd : Bornology.IsBounded C)
    (hA : ∀ (x : ℕ → PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))))
      (x₀ : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b)))),
      (∀ n, x n ∈ C) → x₀ ∈ C →
      (∀ g, Tendsto (fun n => inner ℝ (x n) g) atTop (𝓝 (inner ℝ x₀ g))) →
      Tendsto (fun n => A (x n)) atTop (𝓝 (A x₀))) :
    ∃ h ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (A h) (y - h) := by
  have : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  exact SideConstrainedDTA.Existence.Sol34.lions C A hne hclosed hconv hbdd hA
