-- Prove2me | solution 1 for UnderstandingML.infinite_vc_not_weak_learnable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T15:59:05.710988+00:00
-- url     : https://prove2.me/submissions/c30070f8-1e9a-4969-8c7a-46b63670e76a

import Definitions.Def_UnderstandingML_Boosting


open MeasureTheory

namespace UnderstandingML

section InfiniteVCProof

open Classical in
/-- The counting core of the No-Free-Lunch argument: for a fixed sample of points `x`, summing
over all labelings `g` of a finite set `C` the number of points of `C` on which a (deterministic)
learner errs gives at least `2^|C| (|C| - m) / 2`. -/
lemma nfl_count {C : Type*} [Fintype C] [DecidableEq C] {m : ℕ} (F : (Fin m → C × Bool) → C → Bool)
    (x : Fin m → C) :
    2 ^ Fintype.card C * (Fintype.card C - m) ≤
      2 * ∑ g : C → Bool,
        (Finset.univ.filter fun c ↦ F (fun i ↦ (x i, g (x i))) c ≠ g c).card := by
  -- swap the order of counting
  have hswap : ∑ g : C → Bool,
      (Finset.univ.filter fun c ↦ F (fun i ↦ (x i, g (x i))) c ≠ g c).card =
      ∑ c : C, (Finset.univ.filter fun g : C → Bool ↦
        F (fun i ↦ (x i, g (x i))) c ≠ g c).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  -- for points outside the sample, exactly half of the labelings lead to an error
  have hhalf : ∀ c ∉ Finset.univ.image x, 2 * (Finset.univ.filter fun g : C → Bool ↦
      F (fun i ↦ (x i, g (x i))) c ≠ g c).card = 2 ^ Fintype.card C := by
    intro c hc
    have hxc : ∀ i, x i ≠ c := fun i hi ↦ hc (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    let flip : (C → Bool) → (C → Bool) := fun g ↦ Function.update g c (!g c)
    have hflip_x : ∀ g i, flip g (x i) = g (x i) := fun g i ↦
      Function.update_of_ne (hxc i) _ _
    have hflip_c : ∀ g, flip g c = !g c := fun g ↦ Function.update_self _ _ _
    have hflip2 : ∀ g, flip (flip g) = g := by
      intro g
      funext y
      by_cases hy : y = c
      · subst hy; simp [hflip_c]
      · simp [flip, Function.update_of_ne hy]
    have hsame : ∀ g, (fun i ↦ (x i, flip g (x i))) = (fun i ↦ (x i, g (x i))) := by
      intro g; funext i; rw [hflip_x]
    have hcard : (Finset.univ.filter fun g : C → Bool ↦
        F (fun i ↦ (x i, g (x i))) c ≠ g c).card =
        (Finset.univ.filter fun g : C → Bool ↦
        ¬ F (fun i ↦ (x i, g (x i))) c ≠ g c).card := by
      refine Finset.card_nbij' flip flip ?_ ?_ ?_ ?_
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        rw [hsame, hflip_c]
        cases h1 : F (fun i ↦ (x i, g (x i))) c <;> cases h2 : g c <;> simp_all
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        rw [hsame, hflip_c]
        cases h1 : F (fun i ↦ (x i, g (x i))) c <;> cases h2 : g c <;> simp_all
      · intro g _; exact hflip2 g
      · intro g _; exact hflip2 g
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (C → Bool)))
      (fun g : C → Bool ↦ F (fun i ↦ (x i, g (x i))) c ≠ g c)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at htot
    omega
  calc 2 ^ Fintype.card C * (Fintype.card C - m)
      ≤ 2 ^ Fintype.card C * (Finset.univ \ Finset.univ.image x).card := by
        gcongr
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
        have : (Finset.univ.image x).card ≤ m := by
          simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := x)
        omega
    _ = ∑ c ∈ Finset.univ \ Finset.univ.image x, 2 * (Finset.univ.filter fun g : C → Bool ↦
          F (fun i ↦ (x i, g (x i))) c ≠ g c).card := by
        rw [Finset.sum_congr rfl fun c hc ↦ hhalf c (Finset.mem_sdiff.1 hc).2]
        simp [mul_comm]
    _ ≤ ∑ c : C, 2 * (Finset.univ.filter fun g : C → Bool ↦
          F (fun i ↦ (x i, g (x i))) c ≠ g c).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

variable {X : Type*}

lemma exists_large_shattered (H : Set (X → Bool)) (hvc : vcDim H = ⊤) (n : ℕ) :
    ∃ C : Finset X, Shatters H C ∧ n ≤ C.card := by
  by_contra hcon
  push Not at hcon
  have : vcDim H ≤ n := by
    unfold vcDim
    refine iSup₂_le fun C hC ↦ ?_
    exact_mod_cast (hcon C hC).le
  rw [hvc] at this
  exact absurd this (by simp)

/-- The uniform distribution on a finite set. -/
noncomputable def unifMeas [MeasurableSpace X] (C : Finset X) : Measure X :=
  (C.card : ENNReal)⁻¹ • ∑ c ∈ C, Measure.dirac c

open Classical in
lemma unifMeas_apply [MeasurableSpace X] [MeasurableSingletonClass X] (C : Finset X)
    (s : Set X) :
    unifMeas C s = (C.card : ENNReal)⁻¹ * (C.filter fun c ↦ c ∈ s).card := by
  rw [unifMeas, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.dirac_apply, Set.indicator, Pi.one_apply]
  rw [Finset.card_filter]
  push_cast
  rfl

lemma unifMeas_isProb [MeasurableSpace X] [MeasurableSingletonClass X] (C : Finset X)
    (hC : C.Nonempty) : IsProbabilityMeasure (unifMeas C) := by
  constructor
  rw [unifMeas_apply]
  simp only [Set.mem_univ, Finset.filter_true_of_mem (fun _ _ ↦ trivial)]
  exact ENNReal.inv_mul_cancel (by simpa using hC.ne_empty) (by simp)

open Classical in
lemma card_filter_eq_subtype (C : Finset X) (p : X → Prop) :
    (C.filter p).card = ((Finset.univ : Finset C).filter fun c : C ↦ p c).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact (Finset.sum_coe_sort C (fun x => if p x then 1 else 0)).symm

open Classical in
lemma trueError_unifMeas [MeasurableSpace X] [MeasurableSingletonClass X] (C : Finset X)
    (f h : X → Bool) :
    trueError (unifMeas C) f h =
      (((Finset.univ : Finset C).filter fun c : C ↦ h c ≠ f c).card : ℝ) / C.card := by
  rw [trueError, unifMeas_apply, card_filter_eq_subtype]
  simp only [Set.mem_setOf_eq, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]
  try congr

lemma labeledLaw_unifMeas_singleton [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Finset X) {f : X → Bool} (hf : Measurable f) {c : X} (hc : c ∈ C) :
    labeledLaw (unifMeas C) f {(c, f c)} = (C.card : ENNReal)⁻¹ := by
  have hmeas : Measurable (fun x : X ↦ (x, f x)) := measurable_id.prodMk hf
  rw [labeledLaw, Measure.map_apply hmeas (measurableSet_singleton _)]
  have : (fun x ↦ (x, f x)) ⁻¹' {(c, f c)} = {c} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · exact fun h ↦ h.1
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [this, unifMeas_apply]
  have h1 : ∀ inst : DecidablePred fun x ↦ x ∈ ({c} : Set X),
      (@Finset.filter X (fun x ↦ x ∈ ({c} : Set X)) inst C).card = 1 := by
    intro _
    rw [Finset.card_eq_one]
    refine ⟨c, ?_⟩
    ext x
    simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hc, h⟩⟩
  convert mul_one _
  rw [Nat.cast_eq_one]
  exact h1 _

open Classical in
lemma iidLaw_unifMeas_lower [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Finset X) (hC : C.Nonempty) {f : X → Bool} (hf : Measurable f) (m : ℕ)
    (P : (Fin m → X × Bool) → Prop) :
    ((Finset.univ.filter fun x : Fin m → C ↦ P (fun i ↦ ((x i : X), f (x i)))).card :
        ENNReal) * ((C.card : ENNReal)⁻¹) ^ m ≤
      iidLaw (labeledLaw (unifMeas C) f) m {S | P S} := by
  haveI := unifMeas_isProb C hC
  haveI : IsProbabilityMeasure (labeledLaw (unifMeas C) f) :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk hf).aemeasurable
  set T := Finset.univ.filter fun x : Fin m → C ↦ P (fun i ↦ ((x i : X), f (x i)))
  let emb : (Fin m → C) → (Fin m → X × Bool) := fun x i ↦ ((x i : X), f (x i))
  have hinj : Function.Injective emb := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [emb, Prod.mk.injEq] at this
    exact Subtype.ext this.1
  have hsing : ∀ x : Fin m → C, iidLaw (labeledLaw (unifMeas C) f) m {emb x} =
      ((C.card : ENNReal)⁻¹) ^ m := by
    intro x
    rw [iidLaw, ← Set.univ_pi_singleton, Measure.pi_pi]
    simp only [emb, labeledLaw_unifMeas_singleton C hf (x _).2, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  calc (T.card : ENNReal) * ((C.card : ENNReal)⁻¹) ^ m
      = ∑ x ∈ T, iidLaw (labeledLaw (unifMeas C) f) m {emb x} := by
        rw [Finset.sum_congr rfl fun x _ ↦ hsing x]; simp
    _ = ∑ s ∈ T.image emb, iidLaw (labeledLaw (unifMeas C) f) m {s} :=
        (Finset.sum_image (f := fun s ↦ iidLaw (labeledLaw (unifMeas C) f) m {s})
          fun x _ y _ h ↦ hinj h).symm
    _ = iidLaw (labeledLaw (unifMeas C) f) m ↑(T.image emb) := sum_measure_singleton
    _ ≤ iidLaw (labeledLaw (unifMeas C) f) m {S | P S} := by
        apply measure_mono
        intro s hs
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
        obtain ⟨x, hx, rfl⟩ := hs
        exact (Finset.mem_filter.1 hx).2

end InfiniteVCProof

/-- **§10.1** (p. 132). If `VCdim(H) = ∞` then `H` is not γ-weak-learnable: from the statistical
perspective weak learnability is characterized by the VC-dimension, just as PAC learning is.
(Domain with measurable singletons, measurable hypotheses; the book derives this from the
lower bound of Theorem 6.8 at `ε = 1/2 − γ`, which needs the `km`-point form of the
No-Free-Lunch argument, Exercise 5.3, for `γ` close to `0`.) -/
theorem infinite_vc_not_weak_learnable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hvc : vcDim H = ⊤) {γ : ℝ} (hγ : 0 < γ) : ¬ WeakLearnable H γ := by
  classical
  rintro ⟨A, mH, hA⟩
  -- a smaller advantage `γ' ≤ min γ (1/4)` and the confidence `δ = γ'/4`
  set γ' : ℝ := min γ (1 / 4) with hγ'
  have hγ'0 : 0 < γ' := lt_min hγ (by norm_num)
  have hγ'γ : γ' ≤ γ := min_le_left _ _
  have hγ'4 : γ' ≤ 1 / 4 := min_le_right _ _
  set δ : ℝ := γ' / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by linarith
  set m := mH δ with hm
  -- a large shattered set `C`
  obtain ⟨C, hCsh, hCn⟩ := exists_large_shattered H hvc (⌈(m : ℝ) / γ'⌉₊ + 1)
  set n := C.card with hn
  have hnpos : 0 < n := by omega
  have hCne : C.Nonempty := Finset.card_pos.1 hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnγ : (m : ℝ) < n * γ' := by
    have h1 : (m : ℝ) / γ' ≤ ⌈(m : ℝ) / γ'⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(m : ℝ) / γ'⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hCn
    push_cast at h2
    rw [div_le_iff₀ hγ'0] at h1
    nlinarith
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  haveI := unifMeas_isProb C hCne
  set D := unifMeas C with hD
  -- one hypothesis of `H` for every labeling of `C`
  choose hg hgH hgeq using hCsh
  let S : (C → Bool) → (Fin m → C) → Fin m → X × Bool := fun g x i ↦ ((x i : X), g (x i))
  let k : (C → Bool) → (Fin m → C) → ℕ := fun g x ↦
    (Finset.univ.filter fun c : C ↦ A m (S g x) c ≠ g c).card
  have hk_le : ∀ g x, k g x ≤ n := fun g x ↦ by
    calc k g x ≤ (Finset.univ : Finset C).card := Finset.card_filter_le _ _
      _ = n := by simp [n]
  have hSg : ∀ g x, (fun i ↦ ((x i : X), hg g (x i))) = S g x := by
    intro g x; funext i; simp [S, hgeq]
  have herr : ∀ g x, trueError D (hg g) (A m (S g x)) = (k g x : ℝ) / n := by
    intro g x
    rw [hD, trueError_unifMeas]
    simp only [hgeq]
    rfl
  -- the number of bad samples for each labeling is at most `δ n^m`
  let E : (C → Bool) → ℕ := fun g ↦
    (Finset.univ.filter fun x : Fin m → C ↦ 1 / 2 - γ' < (k g x : ℝ) / n).card
  have hE : ∀ g, (E g : ℝ) ≤ δ * n ^ m := by
    intro g
    have hmeas := hH _ (hgH g)
    have hreal : Realizable H D (hg g) := ⟨hg g, hgH g, by simp [trueError]⟩
    have h1 := hA δ hδ0 hδ1 D inferInstance (hg g) hmeas hreal m le_rfl
    have h2 := iidLaw_unifMeas_lower C hCne hmeas m
      (fun S ↦ 1 / 2 - γ' < trueError D (hg g) (A m S))
    have hEq : (Finset.univ.filter fun x : Fin m → C ↦
        1 / 2 - γ' < trueError D (hg g) (A m (fun i ↦ ((x i : X), hg g (x i))))) =
        Finset.univ.filter fun x : Fin m → C ↦ 1 / 2 - γ' < (k g x : ℝ) / n := by
      refine Finset.filter_congr fun x _ ↦ ?_
      rw [hSg, herr]
    rw [hEq] at h2
    have h3 : iidLaw (labeledLaw D (hg g)) m
        {S | 1 / 2 - γ' < trueError D (hg g) (A m S)} ≤ ENNReal.ofReal δ := by
      refine le_trans (measure_mono fun S hS ↦ ?_) h1
      simp only [Set.mem_setOf_eq] at hS ⊢
      linarith
    have h4 := ENNReal.toReal_le_of_le_ofReal hδ0.le (h2.trans h3)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_natCast] at h4
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at h4
    exact h4
  -- pointwise, the error is at most `1/2 - γ'` plus the indicator of a bad sample
  have hpt : ∀ g x, (k g x : ℝ) / n ≤
      (1 / 2 - γ') + (if 1 / 2 - γ' < (k g x : ℝ) / n then 1 else 0) := by
    intro g x
    have : (k g x : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]; exact_mod_cast hk_le g x
    split_ifs with h
    · linarith
    · linarith [not_lt.1 h]
  have hcardx : (Finset.univ : Finset (Fin m → C)).card = n ^ m := by
    simp [Finset.card_univ, n]
  have hcardg : (Finset.univ : Finset (C → Bool)).card = 2 ^ n := by
    simp [Finset.card_univ, n]
  -- upper bound on the total error
  have hupper : ∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ) / n ≤
      2 ^ n * (n ^ m * (1 / 2 - γ' + δ)) := by
    calc ∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ) / n
        ≤ ∑ g : C → Bool, ∑ x : Fin m → C,
          ((1 / 2 - γ') + (if 1 / 2 - γ' < (k g x : ℝ) / n then 1 else 0)) :=
          Finset.sum_le_sum fun g _ ↦ Finset.sum_le_sum fun x _ ↦ hpt g x
      _ = ∑ g : C → Bool, ((n : ℝ) ^ m * (1 / 2 - γ') + E g) := by
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, hcardx, Finset.sum_boole]
          simp [E, nsmul_eq_mul]
      _ ≤ ∑ g : C → Bool, ((n : ℝ) ^ m * (1 / 2 - γ') + δ * n ^ m) :=
          Finset.sum_le_sum fun g _ ↦ by linarith [hE g]
      _ = 2 ^ n * (n ^ m * (1 / 2 - γ' + δ)) := by
          rw [Finset.sum_const, hcardg, nsmul_eq_mul]; push_cast; ring
  -- lower bound on the total error, from the counting lemma
  have hlower : (n : ℝ) ^ m * (2 ^ n * (n - m)) ≤
      2 * n * ∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ) / n := by
    have hx : ∀ x : Fin m → C, (2 : ℝ) ^ n * (n - m) ≤ 2 * ∑ g : C → Bool, (k g x : ℝ) := by
      intro x
      have h0 := nfl_count (C := C)
        (fun (s : Fin m → C × Bool) c ↦ A m (fun i ↦ (((s i).1 : X), (s i).2)) c) x
      rw [Fintype.card_coe] at h0
      have h1 : 2 ^ n * (n - m) ≤ 2 * ∑ g : C → Bool, k g x := h0
      have h' : ((2 ^ n * (n - m) : ℕ) : ℝ) ≤ ((2 * ∑ g : C → Bool, k g x : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast [Nat.cast_sub hmn] at h'
      exact h'
    calc (n : ℝ) ^ m * (2 ^ n * (n - m)) = ∑ x : Fin m → C, (2 : ℝ) ^ n * (n - m) := by
          rw [Finset.sum_const, hcardx, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ x : Fin m → C, 2 * ∑ g : C → Bool, (k g x : ℝ) := Finset.sum_le_sum fun x _ ↦ hx x
      _ = 2 * n * ∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ) / n := by
          have hdiv : ∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ) / n =
              (∑ g : C → Bool, ∑ x : Fin m → C, (k g x : ℝ)) / n := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun g _ ↦ (Finset.sum_div _ _ _).symm
          rw [hdiv, ← Finset.mul_sum, Finset.sum_comm]
          field_simp
  -- combine: `2 n (γ' - δ) ≤ m`, contradicting `m < n γ'`
  have hP : (0 : ℝ) < 2 ^ n * n ^ m := by positivity
  have key : (2 ^ n * n ^ m : ℝ) * (n - m) ≤ (2 ^ n * n ^ m) * (2 * n * (1 / 2 - γ' + δ)) := by
    have := hlower.trans (mul_le_mul_of_nonneg_left hupper (by positivity))
    nlinarith [this]
  have := le_of_mul_le_mul_left key hP
  nlinarith

end UnderstandingML

open UnderstandingML in
theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hvc : vcDim H = ⊤) {γ : ℝ} (hγ : 0 < γ) : ¬ WeakLearnable H γ :=
  UnderstandingML.infinite_vc_not_weak_learnable H hH hvc hγ

