-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_generating_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:43.113982+00:00
-- url     : https://prove2.me/submissions/06c37a1b-a084-4f17-9189-c2bbc6712ecd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

namespace X7Z10G

variable {k : Type*} [RCLike k]
variable {Z : Type*} [mZ : MeasurableSpace Z]

/-- The sigma-algebra of sets whose indicator lies in `E`. -/
def X7_ME (E : Set (Symbol Z k)) (hE : EightProperties E) : MeasurableSpace Z where
  MeasurableSet' A := ∃ hA : MeasurableSet A, indicator A hA ∈ E
  measurableSet_empty := by
    have h := hE.2.2.2.2.2.2.1.2.1 Set.univ MeasurableSet.univ hE.2.2.2.2.2.2.1.1
    refine ⟨MeasurableSet.empty, ?_⟩
    have heq : indicator (k := k) (∅ : Set Z) MeasurableSet.empty =
        indicator (Set.univ : Set Z)ᶜ MeasurableSet.univ.compl := by
      apply Subtype.ext
      funext x
      simp [indicator]
    rw [heq]
    exact h
  measurableSet_compl A hA := ⟨hA.1.compl, hE.2.2.2.2.2.2.1.2.1 A hA.1 hA.2⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion (fun n => (hf n).1),
      hE.2.2.2.2.2.2.1.2.2 f (fun n => (hf n).1) (fun n => (hf n).2)⟩

theorem X7_ME_le (E : Set (Symbol Z k)) (hE : EightProperties E) : X7_ME E hE ≤ mZ :=
  fun _ hA => hA.1

theorem X7_mem_meas (E : Set (Symbol Z k)) (hE : EightProperties E) (g : Symbol Z k)
    (hg : g ∈ E) : Measurable[X7_ME E hE] g.val :=
  fun B hB => ⟨hB.preimage g.property, hE.2.2.2.2.2.2.2 g hg B hB⟩

theorem X7_simple_mem (E : Set (Symbol Z k)) (hE : EightProperties E)
    (φ : @SimpleFunc Z (X7_ME E hE) k) :
    ∀ h : Measurable (φ : Z → k), (⟨φ, h⟩ : Symbol Z k) ∈ E := by
  induction φ using @SimpleFunc.induction Z k (X7_ME E hE) _ with
  | @const c t hs =>
    intro h
    obtain ⟨hs0, hsE⟩ := hs
    have heq : (⟨_, h⟩ : Symbol Z k) = times (constant c) (indicator _ hs0) := by
      apply Subtype.ext
      funext x
      show Set.piecewise t (fun _ => c) (fun _ => (0 : k)) x = _
      by_cases hx : x ∈ t <;> simp [times, constant, indicator, hx, Set.piecewise]
    rw [heq]
    exact (hE.1.2.1 _ _ (hE.1.1 c) hsE).2
  | add hdisj hf hg =>
    rename_i f g
    intro h
    have hf' : Measurable (f : Z → k) := (@SimpleFunc.measurable Z k (X7_ME E hE) _ f).mono (X7_ME_le E hE) le_rfl
    have hg' : Measurable (g : Z → k) := (@SimpleFunc.measurable Z k (X7_ME E hE) _ g).mono (X7_ME_le E hE) le_rfl
    have heq : (⟨_, h⟩ : Symbol Z k) = plus ⟨f, hf'⟩ ⟨g, hg'⟩ := by
      apply Subtype.ext
      funext x
      simp [plus]
    rw [heq]
    exact (hE.1.2.1 _ _ (hf hf') (hg hg')).1

theorem X7_meas_mem (E : Set (Symbol Z k)) (hE : EightProperties E) (f : Symbol Z k)
    (hf : Measurable[X7_ME E hE] f.val) : f ∈ E := by
  have hs : StronglyMeasurable[X7_ME E hE] f.val :=
    Measurable.stronglyMeasurable (mα := X7_ME E hE) hf
  let fn : ℕ → Symbol Z k := fun n =>
    ⟨hs.approx n, (@SimpleFunc.measurable Z k (X7_ME E hE) _ (hs.approx n)).mono (X7_ME_le E hE) le_rfl⟩
  have hmem : ∀ n, fn n ∈ E := fun n => X7_simple_mem E hE (hs.approx n) _
  exact hE.2.2.2.1 fn f hmem (fun x => hs.tendsto_approx x)

theorem X7_univ_of_le (E : Set (Symbol Z k)) (hE : EightProperties E)
    (hle : mZ ≤ X7_ME E hE) : E = Set.univ := by
  ext f
  simp only [Set.mem_univ, iff_true]
  exact X7_meas_mem E hE f (f.property.mono hle le_rfl)

end X7Z10G

section Main

variable {k : Type*} [RCLike k]

open X7Z10G

theorem X7_le_of_coords {d : ℕ} (S : Set (Fin d → k)) (E : Set (Symbol S k))
    (hE : EightProperties E)
    (h : ∀ j, Measurable[X7_ME E hE] (fun x : S => x.val j)) :
    E = Set.univ := by
  apply X7_univ_of_le E hE
  have hval : Measurable[X7_ME E hE] (Subtype.val : S → Fin d → k) :=
    (@measurable_pi_iff S (Fin d) (fun _ => k) (X7_ME E hE) _ _).mpr h
  exact hval.comap_le

theorem X7_cond1 {d : ℕ} (S : Set (Fin d → k)) (E : Set (Symbol S k))
    (hE : EightProperties E) :
    (E = Set.univ) ↔ ∀ j, restrictedCoordinate S j ∈ E := by
  constructor
  · intro h j; rw [h]; trivial
  · intro h
    exact X7_le_of_coords S E hE (fun j => X7_mem_meas E hE _ (h j))

theorem X7_cond2 {d : ℕ} (S : Set (Fin d → k)) (E : Set (Symbol S k))
    (hE : EightProperties E) :
    (E = Set.univ) ↔ (∀ j, times (restrictedCoordinate S j) (tupleRegularizer S) ∈ E) ∧
      tupleRegularizer S ∈ E := by
  constructor
  · intro h; rw [h]; exact ⟨fun _ => trivial, trivial⟩
  · rintro ⟨h1, h2⟩
    apply X7_le_of_coords S E hE
    intro j
    have m1 := X7_mem_meas E hE _ (h1 j)
    have m2 := X7_mem_meas E hE _ h2
    have heq : (fun x : S => x.val j) = fun x =>
        (times (restrictedCoordinate S j) (tupleRegularizer S)).val x /
          (tupleRegularizer S).val x := by
      funext x
      simp only [times, restrictedCoordinate, tupleRegularizer]
      have hpos : (0 : ℝ) < 1 + squaredTupleNorm x.val := by
        unfold squaredTupleNorm
        have : 0 ≤ ∑ j, ‖x.val j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
        linarith
      have hne : ((1 + squaredTupleNorm x.val : ℝ) : k)⁻¹ ≠ 0 :=
        inv_ne_zero (by exact_mod_cast hpos.ne')
      rw [mul_div_assoc, div_self hne, mul_one]
    rw [heq]
    exact m1.div m2

theorem X7_cond3 {d : ℕ} (S : Set (Fin d → k)) (E : Set (Symbol S k))
    (hE : EightProperties E) :
    (E = Set.univ) ↔ ∀ j, tupleRootCoordinate S j ∈ E := by
  constructor
  · intro h j; rw [h]; trivial
  · intro h
    apply X7_le_of_coords S E hE
    intro j
    have m : ∀ i, Measurable[X7_ME E hE] (tupleRootCoordinate S i).val :=
      fun i => X7_mem_meas E hE _ (h i)
    have heq : (fun x : S => x.val j) = fun x =>
        (tupleRootCoordinate S j).val x /
          ((Real.sqrt (1 - ∑ i, ‖(tupleRootCoordinate S i).val x‖ ^ 2) : ℝ) : k) := by
      funext x
      simp only [tupleRootCoordinate]
      set s := squaredTupleNorm x.val with hs
      have hs0 : 0 ≤ s := Finset.sum_nonneg (fun _ _ => by positivity)
      have hpos : (0 : ℝ) < 1 + s := by linarith
      have hsq : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr hpos
      have hnorm : ∀ i, ‖x.val i / ((Real.sqrt (1 + s) : ℝ) : k)‖ ^ 2 = ‖x.val i‖ ^ 2 / (1 + s) := by
        intro i
        rw [norm_div, RCLike.norm_ofReal, abs_of_pos hsq, div_pow, Real.sq_sqrt hpos.le]
      simp only [hnorm]
      have hsum : ∑ i, ‖x.val i‖ ^ 2 / (1 + s) = s / (1 + s) := by
        rw [← Finset.sum_div]; rfl
      rw [hsum]
      have h1 : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
      rw [h1, Real.sqrt_div' 1 hpos.le, Real.sqrt_one]
      have hk : ((Real.sqrt (1 + s) : ℝ) : k) ≠ 0 := by
        rw [RCLike.ofReal_ne_zero]; exact hsq.ne'
      rw [RCLike.ofReal_div, RCLike.ofReal_one]
      field_simp
    have hg : Measurable[X7_ME E hE] (fun x : S => fun i => (tupleRootCoordinate S i).val x) :=
      (@measurable_pi_iff S (Fin d) (fun _ => k) (X7_ME E hE) _ _).mpr m
    have hΦ : Measurable (fun r : Fin d → k =>
        r j / ((Real.sqrt (1 - ∑ i, ‖r i‖ ^ 2) : ℝ) : k)) := by fun_prop
    rw [heq]
    exact hΦ.comp hg

end Main

end QAlgorithms.Papers.Independent.Claimed50.P05

end

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

open QAlgorithms.Papers.Independent.Claimed50.P05 in
theorem solution {k : Type*} [RCLike k] {d : ℕ} (S : Set (Fin d → k))
    (E : Set (QAlgorithms.Papers.Independent.Claimed50.P05.Symbol S k))
    (hE : EightProperties E) :
    ((E = Set.univ) ↔ ∀ j, restrictedCoordinate S j ∈ E) ∧
    ((E = Set.univ) ↔ (∀ j, times (restrictedCoordinate S j) (tupleRegularizer S) ∈ E) ∧ tupleRegularizer S ∈ E) ∧
    ((E = Set.univ) ↔ ∀ j, tupleRootCoordinate S j ∈ E) :=
  ⟨X7_cond1 S E hE, X7_cond2 S E hE, X7_cond3 S E hE⟩
