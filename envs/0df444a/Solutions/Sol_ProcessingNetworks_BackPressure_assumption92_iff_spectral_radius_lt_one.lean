-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.assumption92_iff_spectral_radius_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:37:54.60737+00:00
-- url     : https://prove2.me/submissions/9d840544-eabe-4c65-9d7d-8bea4bee5acb

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork

open ProcessingNetworks.BackPressure

namespace DaiHHelpers

open scoped ENNReal NNReal Matrix

lemma Qmul_nonneg {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (i : Fin n) : 0 ≤ (Q *ᵥ u) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hQ i j) (hu j))

/-- Maximum principle for `s - Q` with `Q ≥ 0`. -/
lemma maxPrinciple {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (s : ℝ) (hs : 0 < s) (u v : Fin n → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∀ i, 0 < s * u i - (Q *ᵥ u) i) (hv : ∀ i, 0 ≤ s * v i - (Q *ᵥ v) i) :
    ∀ i, 0 ≤ v i := by
  have upos : ∀ i, 0 < u i := by
    intro i
    have h1 := hu i
    have h2 := Qmul_nonneg Q hQ u hu0 i
    have : 0 < s * u i := by linarith
    exact (pos_iff_pos_of_mul_pos this).mp hs
  intro i
  by_contra hneg
  push_neg at hneg
  obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => v i / u i)
    ⟨i, Finset.mem_univ _⟩
  set k := v i0 / u i0 with hkdef
  have hk0 : k < 0 := by
    have := hmin i (Finset.mem_univ _)
    have : v i / u i < 0 := div_neg_of_neg_of_pos hneg (upos i)
    linarith
  have hk : ∀ j, k * u j ≤ v j := by
    intro j
    have := hmin j (Finset.mem_univ _)
    exact (le_div_iff₀ (upos j)).mp this
  have hvi0 : v i0 = k * u i0 := by
    rw [hkdef, div_mul_cancel₀ _ (upos i0).ne']
  have hQv : k * (Q *ᵥ u) i0 ≤ (Q *ᵥ v) i0 := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_left (hk j) (hQ i0 j)
    linarith
  have h3 := hv i0
  have h4 : s * v i0 - (Q *ᵥ v) i0 ≤ k * (s * u i0 - (Q *ᵥ u) i0) := by
    rw [hvi0]; nlinarith
  have h5 : k * (s * u i0 - (Q *ᵥ u) i0) < 0 := mul_neg_of_neg_of_pos hk0 (hu i0)
  linarith

lemma smulOne_mulVec {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (w : Fin n → ℝ) (i : Fin n) :
    ((s • (1 : Matrix (Fin n) (Fin n) ℝ) - Q) *ᵥ w) i = s * w i - (Q *ᵥ w) i := by
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- (⇐) analytic core. -/
lemma exists_nonneg_sol {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdet : ∀ s : ℝ, 1 ≤ s → (s • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).det ≠ 0) :
    ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ ∀ i, z i - (Q *ᵥ z) i = 1 := by
  set A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s => s • (1 : Matrix (Fin n) (Fin n) ℝ) - Q
    with hAdef
  have hAc : Continuous A := (continuous_id.smul continuous_const).sub continuous_const
  set G : ℝ → Fin n → ℝ := fun s => (A s).det⁻¹ • ((A s).adjugate *ᵥ fun _ => 1) with hGdef
  have hG : ∀ s, 1 ≤ s → ∀ i, s * G s i - (Q *ᵥ G s) i = 1 := by
    intro s hs i
    rw [← smulOne_mulVec]
    have hd : (A s).det ≠ 0 := hdet s hs
    have : A s *ᵥ G s = fun _ => 1 := by
      simp only [hGdef, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
        Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
      rw [inv_mul_cancel₀ hd, one_smul]
    exact congrFun this i
  have hGc : ∀ s, 1 ≤ s → ∀ i, ContinuousAt (fun t => G t i) s := by
    intro s hs i
    have h1 : ContinuousAt (fun t => (A t).det⁻¹) s :=
      (hAc.matrix_det.continuousAt).inv₀ (hdet s hs)
    have h2 : Continuous (fun t => ((A t).adjugate *ᵥ fun _ => (1:ℝ)) i) :=
      (continuous_apply i).comp (hAc.matrix_adjugate.matrix_mulVec continuous_const)
    exact h1.mul h2.continuousAt
  let good : ℝ → Prop := fun t => ∀ i, 0 ≤ G t i
  have hstep : ∀ s, 1 ≤ s → ∀ u : Fin n → ℝ, (∀ i, 0 ≤ u i) →
      (∀ i, 0 < s * u i - (Q *ᵥ u) i) → good s := by
    intro s hs u hu0 hu
    exact maxPrinciple Q hQ s (by linarith) u (G s) hu0 hu (fun i => by rw [hG s hs i]; norm_num)
  set s0 : ℝ := 1 + ∑ i, ∑ j, Q i j with hs0
  have hrow : ∀ i, ∑ j, Q i j ≤ ∑ i, ∑ j, Q i j := fun i =>
    Finset.single_le_sum (f := fun i => ∑ j, Q i j)
      (fun i _ => Finset.sum_nonneg (fun j _ => hQ i j)) (Finset.mem_univ i)
  have htot : 0 ≤ ∑ i, ∑ j, Q i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hQ i j))
  let T : Set ℝ := {s | 1 ≤ s ∧ ∀ t, s ≤ t → good t}
  have hs0T : s0 ∈ T := by
    refine ⟨by linarith, fun t ht => ?_⟩
    refine hstep t (by linarith) (fun _ => 1) (fun _ => zero_le_one) (fun i => ?_)
    have : (Q *ᵥ fun _ => (1:ℝ)) i = ∑ j, Q i j := by simp [Matrix.mulVec, dotProduct]
    rw [this]; have := hrow i; linarith
  have hbdd : BddBelow T := ⟨1, fun s hs => hs.1⟩
  have hne : T.Nonempty := ⟨s0, hs0T⟩
  set σ := sInf T with hσ
  have hσ1 : 1 ≤ σ := le_csInf hne (fun s hs => hs.1)
  have habove : ∀ t, σ < t → good t := by
    intro t ht
    obtain ⟨s, hsT, hst⟩ := exists_lt_of_csInf_lt hne ht
    exact hsT.2 t hst.le
  have hgσ : good σ := by
    intro i
    have htend : Filter.Tendsto (fun t => G t i) (nhdsWithin σ (Set.Ioi σ)) (nhds (G σ i)) :=
      (hGc σ hσ1 i).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with t ht using habove t ht i
  have hσeq : σ = 1 := by
    by_contra hne1
    have hσgt : 1 < σ := lt_of_le_of_ne hσ1 (Ne.symm hne1)
    set u := G σ
    set m : ℝ := 1 + ∑ i, u i
    have hsum0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hgσ i)
    have hm : 0 < m := by linarith
    have hum : ∀ i, u i ≤ m := by
      intro i
      have := Finset.single_le_sum (f := u) (fun i _ => hgσ i) (Finset.mem_univ i)
      linarith
    set s' := max 1 (σ - 1 / (2 * m))
    have hs'T : s' ∈ T := by
      refine ⟨le_max_left _ _, fun t ht => ?_⟩
      rcases lt_or_ge t σ with htσ | htσ
      · have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
        refine hstep t ht1 u hgσ (fun i => ?_)
        have hGi := hG σ hσ1 i
        have hd : σ - t ≤ 1 / (2 * m) := by
          have := le_trans (le_max_right _ _) ht; linarith
        have hdu : (σ - t) * u i ≤ 1 / (2 * m) * m :=
          mul_le_mul hd (hum i) (hgσ i) (by positivity)
        have : 1 / (2 * m) * m = 1 / 2 := by field_simp
        nlinarith
      · rcases eq_or_lt_of_le htσ with h | h
        · rw [← h]; exact hgσ
        · exact habove t h
    have h1 : σ ≤ s' := csInf_le hbdd hs'T
    have hpos : 0 < 1 / (2 * m) := by positivity
    have h2 : s' < σ := max_lt hσgt (by linarith)
    linarith
  refine ⟨G 1, fun i => ?_, fun i => ?_⟩
  · have := hgσ i; rwa [hσeq] at this
  · have := hG 1 le_rfl i; simpa using this

/-- (⇒) spectral bound. -/
lemma spectralRadius_lt_one_of {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (z : Fin n → ℝ) (hz0 : ∀ i, 0 ≤ z i) (hz : ∀ i, 0 < z i - (Q *ᵥ z) i) :
    spectralRadius ℝ Q < 1 := by
  have hQz : ∀ i, 0 ≤ (Q *ᵥ z) i := Qmul_nonneg Q hQ z hz0
  have zpos : ∀ i, 0 < z i := fun i => by have := hz i; have := hQz i; linarith
  obtain ⟨c, hc0, hc1, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i, (Q *ᵥ z) i ≤ c * z i := by
    rcases isEmpty_or_nonempty (Fin n) with hE | hE
    · exact ⟨0, le_rfl, zero_lt_one, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ
        (fun i => (Q *ᵥ z) i / z i) Finset.univ_nonempty
      refine ⟨(Q *ᵥ z) i0 / z i0, div_nonneg (hQz i0) (zpos i0).le,
        (div_lt_one (zpos i0)).mpr (by have := hz i0; linarith), fun i => ?_⟩
      exact (div_le_iff₀ (zpos i)).mp (hmax i (Finset.mem_univ _))
  have hspec : ∀ k ∈ spectrum ℝ Q, |k| ≤ c := by
    intro k hk
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not] at hk
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hk
    have hev : ∀ i, k * v i = (Q *ᵥ v) i := by
      intro i
      have := congrFun hv i
      rw [smulOne_mulVec] at this
      simpa [sub_eq_zero] using this
    obtain ⟨i1, hi1⟩ := Function.ne_iff.mp hv0
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i => |v i| / z i) ⟨i1, Finset.mem_univ _⟩
    set M := |v i0| / z i0 with hM
    have hMz : ∀ j, |v j| ≤ M * z j := fun j =>
      (div_le_iff₀ (zpos j)).mp (hmax j (Finset.mem_univ _))
    have hvi0 : 0 < |v i0| := by
      have h1 : 0 < |v i1| / z i1 := div_pos (abs_pos.mpr hi1) (zpos i1)
      have h2 := hmax i1 (Finset.mem_univ _)
      have h3 : 0 < |v i0| / z i0 := lt_of_lt_of_le h1 h2
      exact (div_pos_iff_of_pos_right (zpos i0)).mp h3
    have hMeq : M * z i0 = |v i0| := by rw [hM, div_mul_cancel₀ _ (zpos i0).ne']
    have key : |k| * |v i0| ≤ c * |v i0| := by
      rw [← abs_mul, hev i0]
      calc |(Q *ᵥ v) i0| = |∑ j, Q i0 j * v j| := by simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, |Q i0 j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, Q i0 j * (M * z j) := by
          apply Finset.sum_le_sum; intro j _
          rw [abs_mul, abs_of_nonneg (hQ i0 j)]
          exact mul_le_mul_of_nonneg_left (hMz j) (hQ i0 j)
        _ = M * (Q *ᵥ z) i0 := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ M * (c * z i0) := by
          have hM0 : 0 ≤ M := div_nonneg (abs_nonneg _) (zpos i0).le
          exact mul_le_mul_of_nonneg_left (hc i0) hM0
        _ = c * |v i0| := by rw [← hMeq]; ring
    exact le_of_mul_le_mul_right key hvi0
  have hle : spectralRadius ℝ Q ≤ ((c.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    apply iSup₂_le
    intro k hk
    have h : ‖k‖₊ ≤ c.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc0]
      simpa [Real.norm_eq_abs] using hspec k hk
    exact ENNReal.coe_le_coe.mpr h
  refine lt_of_le_of_lt hle ?_
  have h : c.toNNReal < 1 := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]
    simpa using hc1
  exact ENNReal.coe_lt_one_iff.mpr h

/-- (⇒) combinatorial core: a basis whose columns positively combine to a positive vector. -/
lemma exists_basis {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (x : Fin J → ℝ) (hx0 : ∀ j, 0 ≤ x j) (hx : ∀ i, 0 < (dat.R *ᵥ x) i) :
    ∃ (basis : ActivityBasis dat) (y : Fin I → ℝ), (∀ i, 0 ≤ y i) ∧
      ∀ i, 0 < (basisMatrix basis *ᵥ y) i := by
  classical
  let P : ℕ → Prop := fun n => ∃ x : Fin J → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, 0 < (dat.R *ᵥ x) i) ∧
    (Finset.univ.filter (fun j => x j ≠ 0)).card = n
  have hex : ∃ n, P n := ⟨_, x, hx0, hx, rfl⟩
  obtain ⟨x, hx0, hx, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ x' : Fin J → ℝ, (∀ j, 0 ≤ x' j) → (∀ i, 0 < (dat.R *ᵥ x') i) →
      Nat.find hex ≤ (Finset.univ.filter (fun j => x' j ≠ 0)).card :=
    fun x' h0 h1 => Nat.find_min' hex ⟨x', h0, h1, rfl⟩
  set s := Finset.univ.filter (fun j => x j ≠ 0) with hsdef
  have hmem : ∀ j, j ∈ s ↔ x j ≠ 0 := fun j => by simp [hsdef]
  have hcard : s.card ≤ I := by
    by_contra hlt
    push_neg at hlt
    let f : s → (Fin I → ℝ) := fun j => fun i => dat.R i j
    have hnli : ¬ LinearIndependent ℝ f := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Module.finrank_fin_fun, Fintype.card_coe] at this
      omega
    obtain ⟨g, hg, j1, hj1⟩ := Fintype.not_linearIndependent_iff.mp hnli
    let d : Fin J → ℝ := fun j => if h : j ∈ s then g ⟨j, h⟩ else 0
    have hds : ∀ j, j ∉ s → d j = 0 := fun j hj => by simp [d, hj]
    have hRd : dat.R *ᵥ d = 0 := by
      funext i
      have hgi := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at hgi
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by rw [hds j hj, mul_zero]),
        ← Finset.sum_coe_sort s]
      rw [← hgi]
      apply Finset.sum_congr rfl
      intro j _
      simp [d, mul_comm]
    obtain ⟨e, hRe, hes, je, hje⟩ : ∃ e : Fin J → ℝ, dat.R *ᵥ e = 0 ∧ (∀ j, j ∉ s → e j = 0) ∧
        ∃ j, e j < 0 := by
      have hd1 : d j1 ≠ 0 := by simpa [d] using hj1
      rcases lt_or_gt_of_ne hd1 with h | h
      · exact ⟨d, hRd, hds, j1, h⟩
      · refine ⟨-d, by rw [Matrix.mulVec_neg, hRd, neg_zero], fun j hj => by
          simp [hds j hj], j1, by simpa using h⟩
    set N := Finset.univ.filter (fun j => e j < 0)
    have hNne : N.Nonempty := ⟨je, by simp [N, hje]⟩
    obtain ⟨j0, hj0N, hjmin⟩ := Finset.exists_min_image N (fun j => x j / (-e j)) hNne
    have hj0 : e j0 < 0 := by simpa [N] using hj0N
    have hNs : ∀ j, e j < 0 → 0 < x j := by
      intro j hj
      have : j ∈ s := by
        by_contra hjs; rw [hes j hjs] at hj; exact lt_irrefl _ hj
      exact lt_of_le_of_ne (hx0 j) (Ne.symm ((hmem j).mp this))
    set t := x j0 / (-e j0)
    have ht0 : 0 ≤ t := div_nonneg (hx0 j0) (by linarith)
    let x' : Fin J → ℝ := x + t • e
    have hx'j : ∀ j, x' j = x j + t * e j := fun j => rfl
    have hx'0 : ∀ j, 0 ≤ x' j := by
      intro j
      rw [hx'j]
      rcases lt_or_ge (e j) 0 with h | h
      · have := hjmin j (by simp [N, h])
        have := (le_div_iff₀ (by linarith : 0 < -e j)).mp this
        linarith
      · exact add_nonneg (hx0 j) (mul_nonneg ht0 h)
    have hRx' : dat.R *ᵥ x' = dat.R *ᵥ x := by
      simp only [x', Matrix.mulVec_add, Matrix.mulVec_smul, hRe, smul_zero, add_zero]
    have hsub : Finset.univ.filter (fun j => x' j ≠ 0) ⊆ s.erase j0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        apply hj
        rw [hx'j]
        have : e j ≠ 0 := hj0.ne
        simp only [t]; field_simp; ring
      · by_contra hjs
        apply hj
        rw [hx'j, hes j hjs, mul_zero, add_zero]
        by_contra hxj
        exact hjs ((hmem j).mpr hxj)
    have h1 := hmin x' hx'0 (by rw [hRx']; exact hx)
    have h2 := Finset.card_le_card hsub
    have hj0s : j0 ∈ s := (hmem j0).mpr (hNs j0 hj0).ne'
    rw [Finset.card_erase_of_mem hj0s] at h2
    have : s.card = Nat.find hex := hxc
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨j0, hj0s⟩
    omega
  have hserve : ∀ i, ∃ j ∈ s, 0 < dat.R i j := by
    intro i
    by_contra h
    push_neg at h
    have := hx i
    have hle : (dat.R *ᵥ x) i ≤ 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_nonpos
      intro j _
      by_cases hj : j ∈ s
      · exact mul_nonpos_of_nonpos_of_nonneg (h j hj) (hx0 j)
      · have : x j = 0 := by by_contra hh; exact hj ((hmem j).mpr hh)
        rw [this, mul_zero]
    linarith
  choose ch hchs hchpos using hserve
  have hinj : Function.Injective ch := by
    intro i i' hii'
    have h1 := hchpos i
    have h2 := hchpos i'
    rw [← hii'] at h2
    exact (h91 (ch i)).unique h1 h2
  let basis : ActivityBasis dat := ⟨ch, hinj, hchpos⟩
  have himg : Finset.univ.image ch = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      exact hchs i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      exact hcard
  refine ⟨basis, fun i => x (ch i), fun i => hx0 _, fun i => ?_⟩
  have : (basisMatrix basis *ᵥ fun i => x (ch i)) i = (dat.R *ᵥ x) i := by
    simp only [Matrix.mulVec, dotProduct, basisMatrix, basis]
    rw [← Finset.sum_image (f := fun j => dat.R i j * x j) (fun a _ b _ h => hinj h), himg]
    apply Finset.sum_subset (Finset.subset_univ s)
    intro j _ hj
    have : x j = 0 := by by_contra hh; exact hj ((hmem j).mpr hh)
    rw [this, mul_zero]
  rw [this]; exact hx i

end DaiHHelpers

open DaiHHelpers in
open scoped Matrix ENNReal NNReal in
theorem solution
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat) :
    SatisfiesAssumption92 dat ↔
      ∃ (basis : ActivityBasis dat) (Q : Matrix (Fin I) (Fin I) ℝ) (Δ : Fin I → ℝ),
        IsBasisDecomposition (basisMatrix basis) Q Δ ∧
        spectralRadius ℝ Q < 1 := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨basis, y, hy0, hy⟩ := exists_basis dat h91 x hx0 hx
    set Rh := basisMatrix basis with hRh
    have hdpos : ∀ i, 0 < Rh i i := fun i => basis.serves i
    set Δ : Fin I → ℝ := fun i => (Rh i i)⁻¹ with hΔ
    have hΔpos : ∀ i, 0 < Δ i := fun i => inv_pos.mpr (hdpos i)
    set Q : Matrix (Fin I) (Fin I) ℝ := 1 - Rh * Matrix.diagonal Δ with hQdef
    have h1Q : 1 - Q = Rh * Matrix.diagonal Δ := by rw [hQdef, sub_sub_cancel]
    have hQ : ∀ i i', 0 ≤ Q i i' := by
      intro i i'
      simp only [hQdef, Matrix.sub_apply, Matrix.mul_diagonal]
      by_cases h : i = i'
      · subst h
        simp only [Matrix.one_apply_eq, hΔ]
        rw [mul_inv_cancel₀ (hdpos i).ne', sub_self]
      · rw [Matrix.one_apply_ne h, zero_sub, neg_nonneg]
        have hle : Rh i i' ≤ 0 := by
          by_contra hh
          push_neg at hh
          exact h ((h91 (basis.choice i')).unique hh (basis.serves i'))
        exact mul_nonpos_of_nonpos_of_nonneg hle (hΔpos i').le
    set z : Fin I → ℝ := fun i => Rh i i * y i with hz
    have hz0 : ∀ i, 0 ≤ z i := fun i => mul_nonneg (hdpos i).le (hy0 i)
    have hDz : Matrix.diagonal Δ *ᵥ z = y := by
      funext i
      rw [Matrix.mulVec_diagonal, hΔ, hz]
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ (hdpos i).ne', one_mul]
    have hzQ : ∀ i, 0 < z i - (Q *ᵥ z) i := by
      intro i
      have : z i - (Q *ᵥ z) i = ((1 - Q) *ᵥ z) i := by
        simp [Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [this, h1Q, ← Matrix.mulVec_mulVec, hDz]
      exact hy i
    refine ⟨basis, Q, Δ, ⟨hΔpos, hQ, ?_⟩, spectralRadius_lt_one_of Q hQ z hz0 hzQ⟩
    rw [h1Q, mul_assoc, Matrix.diagonal_mul_diagonal]
    have : (fun i => Δ i * (Δ i)⁻¹) = fun _ => (1:ℝ) := by
      funext i; exact mul_inv_cancel₀ (hΔpos i).ne'
    rw [this, Matrix.diagonal_one, mul_one]
  · rintro ⟨basis, Q, Δ, ⟨hΔ, hQ, hdec⟩, hρ⟩
    have hdet : ∀ s : ℝ, 1 ≤ s → (s • (1 : Matrix (Fin I) (Fin I) ℝ) - Q).det ≠ 0 := by
      intro s hs h0
      have hmem : s ∈ spectrum ℝ Q := by
        rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det, h0]
        exact not_isUnit_zero
      have hle : ((‖s‖₊ : ℝ≥0) : ℝ≥0∞) ≤ spectralRadius ℝ Q :=
        le_iSup₂ (f := fun k (_ : k ∈ spectrum ℝ Q) => ((‖k‖₊ : ℝ≥0) : ℝ≥0∞)) s hmem
      have h1 : (1 : ℝ≥0∞) ≤ ((‖s‖₊ : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.one_le_coe_iff, ← NNReal.coe_le_coe]
        simp only [NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
        exact le_trans hs (le_abs_self s)
      exact absurd (lt_of_le_of_lt (h1.trans hle) hρ) (lt_irrefl _)
    obtain ⟨z, hz0, hz⟩ := exists_nonneg_sol Q hQ hdet
    classical
    let x : Fin J → ℝ := fun j => ∑ i, if basis.choice i = j then Δ i * z i else 0
    refine ⟨x, fun j => Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact mul_nonneg (hΔ i).le (hz0 i)
      · exact le_rfl), fun i => ?_⟩
    have key : (dat.R *ᵥ x) i = (basisMatrix basis *ᵥ fun i => Δ i * z i) i := by
      simp only [Matrix.mulVec, dotProduct, x, basisMatrix, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.sum_ite_eq]
      simp
    rw [key, hdec, ← Matrix.mulVec_mulVec]
    have hD : (Matrix.diagonal fun i => (Δ i)⁻¹) *ᵥ (fun i => Δ i * z i) = z := by
      funext i
      rw [Matrix.mulVec_diagonal, ← mul_assoc, inv_mul_cancel₀ (hΔ i).ne', one_mul]
    rw [hD]
    have : ((1 - Q) *ᵥ z) i = z i - (Q *ᵥ z) i := by
      simp [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [this, hz i]
    exact one_pos
