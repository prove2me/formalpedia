-- Prove2me | solution 1 for SennottDP.ContinuousTime.asm_optimal_ctmdc_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:42:44.205239+00:00
-- url     : https://prove2.me/submissions/8d30ee76-2d90-47d2-87b7-f966f4211dd2

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

set_option autoImplicit false

open scoped ENNReal
open Filter Topology MeasureTheory ProbabilityTheory

namespace SennottDP.ContinuousTime.Ebeb

open SennottDP.ContinuousTime

/-- CT-D. -/
theorem aux_isValid {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) : (Ψ.aux tau).IsValid := by
  classical
  obtain ⟨htau, ⟨ε, hε, hε'⟩, -⟩ := hCTB
  obtain ⟨hA, hpos, hP1, hP0⟩ := hΨ
  refine ⟨hA, fun i a ha => ?_, fun i a ha => ?_⟩
  · obtain ⟨hG, hg, hν⟩ := hpos i a ha
    show 0 ≤ Ψ.G i a * Ψ.ν i a + Ψ.g i a
    positivity
  · have hν := (hpos i a ha).2.2
    have h := hε' i a ha
    unfold CTMDC.meanSojourn at h
    have h2 : tau < 1 / Ψ.ν i a := by linarith
    rw [lt_div_iff₀ hν] at h2
    have h0 : 0 ≤ tau * Ψ.ν i a := (mul_pos htau hν).le
    have hf : ∀ j, (Ψ.aux tau).P i a j =
        (if j = i then ENNReal.ofReal (1 - tau * Ψ.ν i a) else 0) +
          ENNReal.ofReal (tau * Ψ.ν i a) * Ψ.P i a j := by
      intro j
      simp only [CTMDC.aux]
      by_cases hj : j = i
      · subst hj; simp [hP0 j a ha]
      · simp [hj]
    simp_rw [hf]
    rw [ENNReal.tsum_add, tsum_ite_eq, ENNReal.tsum_mul_left, hP1 i a ha, mul_one,
      ← ENNReal.ofReal_add (by linarith) h0]
    simp


/-- CT-C. -/
theorem exists_subseq_limit_ct' {S Act : Type} [Countable S] {M : MDC S Act} (Δs : ApproxSeq M)
    (eN : ℕ → S → Act) (hmem : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, eN N i ∈ M.A i)
    (φ : ℕ → ℕ) (hφt : Tendsto φ atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ estar : S → Act, (∀ i, estar i ∈ M.A i) ∧
      ∀ i, ∀ᶠ r in atTop, eN (φ (ψ r)) i = estar i := by
  classical
  let _ : ∀ i, TopologicalSpace (M.A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (M.A i) := fun _ => ⟨rfl⟩
  have hcov : ∀ i, ∃ N, Δs.N0 ≤ N ∧ i ∈ Δs.SN N := Δs.SN_cover
  let d : ∀ i, M.A i := fun i =>
    ⟨eN (hcov i).choose i, hmem _ (hcov i).choose_spec.1 i (hcov i).choose_spec.2⟩
  let x : ℕ → (∀ i, M.A i) := fun r i => if h : eN (φ r) i ∈ M.A i then ⟨eN (φ r) i, h⟩ else d i
  obtain ⟨a, ψ, hψ, hlim⟩ := CompactSpace.tendsto_subseq x
  refine ⟨ψ, hψ, fun i => (a i).1, fun i => (a i).2, fun i => ?_⟩
  have h1 := (continuous_apply i).continuousAt.tendsto.comp hlim
  rw [nhds_discrete, tendsto_pure] at h1
  obtain ⟨N₁, hN₁0, hN₁⟩ := hcov i
  have h2 : ∀ᶠ k in atTop, N₁ ≤ φ (ψ k) :=
    (hφt.comp hψ.tendsto_atTop).eventually (eventually_ge_atTop N₁)
  filter_upwards [h1, h2] with k hk hk2
  have hm : eN (φ (ψ k)) i ∈ M.A i :=
    hmem (φ (ψ k)) (le_trans hN₁0 hk2) i (Δs.SN_mono N₁ (φ (ψ k)) hN₁0 hk2 hN₁)
  have : x (ψ k) i = a i := hk
  simp only [x, dif_pos hm] at this
  exact congrArg Subtype.val this



/-- CT-C as in the plan (StrictMono). -/
theorem exists_subseq_limit_ct {S Act : Type} [Countable S] {M : MDC S Act} (Δs : ApproxSeq M)
    (eN : ℕ → S → Act) (hmem : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, eN N i ∈ M.A i)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ estar : S → Act, (∀ i, estar i ∈ M.A i) ∧
      ∀ i, ∀ᶠ r in atTop, eN (φ (ψ r)) i = estar i :=
  exists_subseq_limit_ct' Δs eN hmem φ hφ.tendsto_atTop


section CTA

variable {S Act : Type} (M : MDC S Act) (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i : S)

/-- t-step marginal of the stationary chain. -/
noncomputable def qm (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' h, MDC.histProb (M.ofStationary e he) i t h j

open Classical in
lemma qm_zero (j : S) : qm M e he i 0 j = if j = i then 1 else 0 := by
  classical
  unfold qm
  rw [tsum_eq_single []]
  · rfl
  · intro h hh
    cases h with
    | nil => exact absurd rfl hh
    | cons p h => rfl

lemma qm_succ (t : ℕ) (j : S) :
    qm M e he i (t + 1) j = ∑' k, qm M e he i t k * M.P k (e k) j := by
  classical
  unfold qm
  have hinj : Function.Injective (fun p : (S × Act) × List (S × Act) => p.1 :: p.2) := by
    intro p q hpq
    simp only [List.cons.injEq] at hpq
    exact Prod.ext hpq.1 hpq.2
  rw [← hinj.tsum_eq]
  swap
  · intro h hh
    cases h with
    | nil => exact absurd rfl hh
    | cons p h => exact ⟨(p, h), rfl⟩
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
  congr 1; funext k
  have : ∀ a, ∑' h, MDC.histProb (M.ofStationary e he) i (t + 1) ((k, a) :: h) j =
      if a = e k then (∑' h, MDC.histProb (M.ofStationary e he) i t h k) * M.P k (e k) j
      else 0 := by
    intro a
    simp only [MDC.histProb, MDC.ofStationary]
    split_ifs with ha
    · subst ha; simp [ENNReal.tsum_mul_right]
    · simp
  simp_rw [this]
  rw [tsum_ite_eq]

lemma qm_sum (hM : M.IsValid) (t : ℕ) : ∑' j, qm M e he i t j = 1 := by
  classical
  induction t with
  | zero => simp_rw [qm_zero]; simp
  | succ t ih =>
    simp_rw [qm_succ]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hM.2.2 _ _ (he _), mul_one, ih]

lemma expectedCost_eq (t : ℕ) :
    MDC.expectedCost (M.ofStationary e he) i t =
      ∑' j, qm M e he i t j * ENNReal.ofReal (M.C j (e j)) := by
  classical
  unfold MDC.expectedCost qm
  have : ∀ h j, ∑ a ∈ M.A j, MDC.histProb (M.ofStationary e he) i t h j *
      (M.ofStationary e he).σ h j a * ENNReal.ofReal (M.C j a) =
      MDC.histProb (M.ofStationary e he) i t h j * ENNReal.ofReal (M.C j (e j)) := by
    intro h j
    simp only [MDC.ofStationary, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (M.A j) (e j), if_pos (he j)]
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]

lemma ofReal_step (x y J : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ J + y) :
    ENNReal.ofReal x + ENNReal.ofReal (-J) ≤ ENNReal.ofReal J + ENNReal.ofReal y := by
  rcases le_or_gt 0 J with hJ | hJ
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -J ≤ 0), add_zero,
      ← ENNReal.ofReal_add hJ hy]
    exact ENNReal.ofReal_le_ofReal h
  · rw [ENNReal.ofReal_of_nonpos hJ.le, zero_add, ← ENNReal.ofReal_add hx (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end CTA

/-- CT-A. -/
theorem avgCost_le_of_acoi {S Act : Type} [Countable S] (M : MDC S Act) (hM : M.IsValid)
    (e : S → Act) (he : ∀ i, e i ∈ M.A i) (J : ℝ) (w : S → ℝ) (hw : BddBelow (Set.range w))
    (hsum : ∀ i, Summable (fun j => (M.P i (e i) j).toReal * w j))
    (hacoi : ∀ i, M.C i (e i) + ∑' j, (M.P i (e i) j).toReal * w j ≤ J + w i) :
    ∀ i, ((M.avgCost (M.ofStationary e he) i : ℝ≥0∞) : EReal) ≤ (J : EReal) := by
  classical
  intro i
  obtain ⟨m, hm⟩ := hw
  have hm' : ∀ k, m ≤ w k := fun k => hm ⟨k, rfl⟩
  set v : S → ℝ := fun k => w k - m with hv
  have hv0 : ∀ k, 0 ≤ v k := fun k => by simp [hv, hm' k]
  have hPne : ∀ j k, M.P j (e j) k ≠ ⊤ := by
    intro j k h
    have h1 := hM.2.2 j (e j) (he j)
    have h2 : M.P j (e j) k ≤ ∑' k, M.P j (e j) k := ENNReal.le_tsum k
    rw [h, h1] at h2
    exact absurd h2 (by simp)
  have hPsum : ∀ j, Summable (fun k => (M.P j (e j) k).toReal) := fun j =>
    ENNReal.summable_toReal (by rw [hM.2.2 j (e j) (he j)]; simp)
  have hP1 : ∀ j, ∑' k, (M.P j (e j) k).toReal = 1 := by
    intro j
    rw [← ENNReal.tsum_toReal_eq (hPne j), hM.2.2 j (e j) (he j)]; simp
  have hvsum : ∀ j, Summable (fun k => (M.P j (e j) k).toReal * v k) := by
    intro j
    exact ((hsum j).sub ((hPsum j).mul_right m)).congr (fun k => by simp [hv]; ring)
  have hvt : ∀ j, ∑' k, (M.P j (e j) k).toReal * v k =
      ∑' k, (M.P j (e j) k).toReal * w k - m := by
    intro j
    have := (hsum j).tsum_sub ((hPsum j).mul_right m)
    rw [tsum_mul_right, hP1 j, one_mul] at this
    rw [← this]; congr 1; funext k; simp [hv]; ring
  -- ENNReal form of P v
  have hPv : ∀ j, ∑' k, M.P j (e j) k * ENNReal.ofReal (v k) =
      ENNReal.ofReal (∑' k, (M.P j (e j) k).toReal * v k) := by
    intro j
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (hv0 k))
      (hvsum j)]
    congr 1; funext k
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hPne j k)]
  have hC0 : ∀ j, 0 ≤ M.C j (e j) := fun j => hM.2.1 j (e j) (he j)
  have hPv0 : ∀ j, 0 ≤ ∑' k, (M.P j (e j) k).toReal * v k := fun j =>
    tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (hv0 k))
  have hstep : ∀ j, ENNReal.ofReal (M.C j (e j)) +
      ∑' k, M.P j (e j) k * ENNReal.ofReal (v k) + ENNReal.ofReal (-J) ≤
      ENNReal.ofReal J + ENNReal.ofReal (v j) := by
    intro j
    rw [hPv j, ← ENNReal.ofReal_add (hC0 j) (hPv0 j)]
    apply ofReal_step _ _ _ (add_nonneg (hC0 j) (hPv0 j)) (hv0 j)
    rw [hvt j]; simp only [hv]; linarith [hacoi j]
  -- telescoping
  set q := qm M e he i with hq
  set c : ℕ → ℝ≥0∞ := fun t => MDC.expectedCost (M.ofStationary e he) i t with hc
  set D : ℕ → ℝ≥0∞ := fun t => ∑' j, q t j * ENNReal.ofReal (v j) with hD
  have hDsucc : ∀ t, D (t + 1) =
      ∑' j, q t j * ∑' k, M.P j (e j) k * ENNReal.ofReal (v k) := by
    intro t
    simp only [hD, hq, qm_succ]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; funext j
    rw [← ENNReal.tsum_mul_left]; congr 1; funext k; ring
  have hone : ∀ t, ∑' j, q t j = 1 := fun t => qm_sum M e he i hM t
  have htel1 : ∀ t, c t + D (t + 1) + ENNReal.ofReal (-J) ≤ ENNReal.ofReal J + D t := by
    intro t
    have h1 : c t + D (t + 1) + ENNReal.ofReal (-J) =
        ∑' j, q t j * (ENNReal.ofReal (M.C j (e j)) +
          ∑' k, M.P j (e j) k * ENNReal.ofReal (v k) + ENNReal.ofReal (-J)) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hone t, one_mul,
        hDsucc t, hc]
      simp only [expectedCost_eq, hq]
    have h2 : ENNReal.ofReal J + D t =
        ∑' j, q t j * (ENNReal.ofReal J + ENNReal.ofReal (v j)) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hone t, one_mul]
    rw [h1, h2]
    exact ENNReal.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hstep j) (zero_le))
  have htel : ∀ n : ℕ, (∑ t ∈ Finset.range n, c t) + D n + n * ENNReal.ofReal (-J) ≤
      n * ENNReal.ofReal J + D 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (∑ t ∈ Finset.range (n + 1), c t) + D (n + 1) + ((n + 1 : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (-J)
          = (∑ t ∈ Finset.range n, c t) + n * ENNReal.ofReal (-J) +
              (c n + D (n + 1) + ENNReal.ofReal (-J)) := by
            rw [Finset.sum_range_succ]; push_cast; ring
        _ ≤ (∑ t ∈ Finset.range n, c t) + n * ENNReal.ofReal (-J) +
              (ENNReal.ofReal J + D n) := add_le_add le_rfl (htel1 n)
        _ = ((∑ t ∈ Finset.range n, c t) + D n + n * ENNReal.ofReal (-J)) +
              ENNReal.ofReal J := by ring
        _ ≤ (n * ENNReal.ofReal J + D 0) + ENNReal.ofReal J := add_le_add ih le_rfl
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal J + D 0 := by push_cast; ring
  have hD0 : D 0 = ENNReal.ofReal (v i) := by
    simp only [hD, hq, qm_zero, ite_mul, one_mul, zero_mul]
    rw [tsum_ite_eq]
  rcases lt_or_ge J 0 with hJ | hJ
  · exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt (v i / -J)
    have h' : (n : ℝ≥0∞) * ENNReal.ofReal (-J) ≤ ENNReal.ofReal (v i) := by
      have := htel n
      rw [ENNReal.ofReal_of_nonpos hJ.le, mul_zero, zero_add, hD0] at this
      exact le_trans le_add_self this
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (hv0 i)] at h'
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith
  · have hle : M.avgCost (M.ofStationary e he) i ≤ ENNReal.ofReal J := by
      unfold MDC.avgCost
      have hT : Tendsto (fun n : ℕ => ENNReal.ofReal J + ENNReal.ofReal (v i) / n) atTop
          (𝓝 (ENNReal.ofReal J)) := by
        have : Tendsto (fun n : ℕ => ENNReal.ofReal (v i) * (n : ℝ≥0∞)⁻¹) atTop
            (𝓝 (ENNReal.ofReal (v i) * 0)) :=
          ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr ENNReal.ofReal_ne_top)
        rw [mul_zero] at this
        simpa [div_eq_mul_inv] using tendsto_const_nhds.add this
      rw [← hT.limsup_eq]
      apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      apply ENNReal.div_le_of_le_mul
      rw [add_mul, ENNReal.div_mul_cancel hn0 (ENNReal.natCast_ne_top n), mul_comm, ← hD0]
      exact le_trans (le_trans le_self_add le_self_add) (htel n)
    calc ((M.avgCost (M.ofStationary e he) i : ℝ≥0∞) : EReal)
        ≤ ((ENNReal.ofReal J : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle
      _ = (J : EReal) := by rw [EReal.coe_ennreal_ofReal, max_eq_left hJ]



lemma tsum_fatou' {S : Type} (b : ℕ → S → ℝ≥0∞) :
    ∑' j, liminf (fun N => b N j) atTop ≤ liminf (fun N => ∑' j, b N j) atTop := by
  let _ : MeasurableSpace S := ⊤
  rw [← MeasureTheory.lintegral_count' (measurable_from_top)]
  have h := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count)
    (u := atTop) (f := b) (fun n => measurable_from_top)
  refine h.trans (le_of_eq ?_)
  congr 1; funext N
  exact MeasureTheory.lintegral_count' measurable_from_top

/-- CT-B. -/
theorem limit_acoi_ct' {S Act : Type} [Countable S] {M : MDC S Act} (hM : M.IsValid)
    (Δs : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, -Q ≤ rN N i)
    (eN : ℕ → S → Act) (hmin : Δs.RealizesMin JN rN eN)
    (φ : ℕ → ℕ) (hφt : Tendsto φ atTop atTop) (estar : S → Act)
    (hlim : ∀ i, ∀ᶠ r in atTop, eN (φ r) i = estar i)
    (J0 : ℝ) (hJ : Tendsto (fun r => JN (φ r)) atTop (𝓝 J0)) :
    ∃ w : S → ℝ, (∀ i, -Q ≤ w i) ∧
      ∀ i, Summable (fun j => (M.P i (estar i) j).toReal * w j) ∧
        M.C i (estar i) + ∑' j, (M.P i (estar i) j).toReal * w j ≤ J0 + w i := by
  classical
  have hev : ∀ j, ∀ᶠ r in atTop, Δs.N0 ≤ φ r ∧ j ∈ Δs.SN (φ r) := by
    intro j
    obtain ⟨N₁, h1, h2⟩ := Δs.SN_cover j
    filter_upwards [hφt.eventually (eventually_ge_atTop N₁)] with r hr
    exact ⟨h1.trans hr, Δs.SN_mono N₁ (φ r) h1 hr h2⟩
  set y : ℕ → S → ℝ≥0∞ := fun r j => ENNReal.ofReal (rN (φ r) j + Q) with hy
  set W : S → ℝ≥0∞ := fun j => liminf (fun r => y r j) atTop with hW
  have hWfin : ∀ j, W j ≠ ⊤ := by
    intro j
    obtain ⟨U, hU1, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hAC.2.1 j)
    have h1 := eventually_lt_of_limsup_lt hU1
    have h2 : ∀ᶠ r in atTop, y r j ≤ ENNReal.ofReal (U + Q) := by
      filter_upwards [hφt.eventually h1] with r hr
      have : rN (φ r) j < U := by exact_mod_cast hr
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have : W j ≤ ENNReal.ofReal (U + Q) :=
      liminf_le_of_frequently_le' h2.frequently
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  have hmemA : ∀ i, estar i ∈ M.A i := by
    intro i
    obtain ⟨r, hr1, hr2⟩ := ((hev i).and (hlim i)).exists
    rw [← hr2]
    exact (hmin (φ r) hr1.1 i hr1.2).1
  -- the main inequality, with a margin δ
  have key : ∀ i, ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (M.C i (estar i)) + ∑' j, M.P i (estar i) j * W j +
          ENNReal.ofReal (|J0| + 1) ≤
        ENNReal.ofReal (J0 + δ + (|J0| + 1)) + W i := by
    intro i δ hδ
    set a := estar i with ha_def
    set K : ℝ := |J0| + 1 with hK
    have hK0 : 0 ≤ K := by positivity
    have hJK : 0 ≤ J0 + δ + K := by
      have := neg_abs_le J0; linarith
    set F : ℕ → ℝ≥0∞ := fun r => ∑' j, (if j ∈ Δs.SN (φ r) then
      Δs.PN (φ r) i a j * y r j else 0) with hF
    have hJev : ∀ᶠ r in atTop, JN (φ r) ≤ J0 + δ :=
      (hJ.eventually (gt_mem_nhds (by linarith : J0 < J0 + δ))).mono fun r hr => hr.le
    have hstep : ∀ᶠ r in atTop, ENNReal.ofReal (M.C i a) + F r + ENNReal.ofReal K ≤
        ENNReal.ofReal (J0 + δ + K) + y r i := by
      filter_upwards [hev i, hlim i, hJev] with r hr hre hrJ
      obtain ⟨hN0, hiS⟩ := hr
      set N := φ r
      have hbr := (hmin N hN0 i hiS).2
      rw [hre] at hbr
      unfold ApproxSeq.bracket at hbr
      have hsum1 := Δs.PN_sum N hN0 i hiS a (hmemA i)
      have hPNne : ∀ j ∈ Δs.SN N, Δs.PN N i a j ≠ ⊤ := by
        intro j hj h
        have : Δs.PN N i a j ≤ ∑ k ∈ Δs.SN N, Δs.PN N i a k :=
          Finset.single_le_sum (fun _ _ => zero_le) hj
        rw [h, hsum1] at this
        exact absurd this (by simp)
      have hsumR : ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal = 1 := by
        rw [← ENNReal.toReal_sum hPNne, hsum1]; simp
      have hnn : ∀ j ∈ Δs.SN N, 0 ≤ rN N j + Q := fun j hj => by
        have := hQ N hN0 j hj; linarith
      have hFeq : F r = ∑ j ∈ Δs.SN N, Δs.PN N i a j * y r j := by
        simp only [hF]
        rw [tsum_eq_sum (s := Δs.SN N) (fun j hj => if_neg hj)]
        exact Finset.sum_congr rfl (fun j hj => if_pos hj)
      have hFR : F r = ENNReal.ofReal (∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * (rN N j + Q)) := by
        rw [hFeq, ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg ENNReal.toReal_nonneg
          (hnn j hj))]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hPNne j hj)]
      have hR : ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * (rN N j + Q) =
          ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * rN N j + Q := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsumR, one_mul]
      have hC0 : 0 ≤ M.C i a := hM.2.1 i a (hmemA i)
      have hS0 : 0 ≤ ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * (rN N j + Q) :=
        Finset.sum_nonneg (fun j hj => mul_nonneg ENNReal.toReal_nonneg (hnn j hj))
      rw [hFR, ← ENNReal.ofReal_add hC0 hS0, ← ENNReal.ofReal_add (add_nonneg hC0 hS0) hK0,
        ← ENNReal.ofReal_add hJK (hnn i hiS)]
      apply ENNReal.ofReal_le_ofReal
      rw [hR]
      linarith
    -- liminf of both sides
    have hlow : ENNReal.ofReal (M.C i a) + ∑' j, M.P i a j * W j + ENNReal.ofReal K ≤
        liminf (fun r => ENNReal.ofReal (M.C i a) + F r + ENNReal.ofReal K) atTop := by
      rw [liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault),
        liminf_const_add atTop _ _ (by isBoundedDefault) (by isBoundedDefault)]
      gcongr
      refine le_trans ?_ (tsum_fatou' _)
      refine ENNReal.tsum_le_tsum fun j => ?_
      have hc : liminf (fun r => if j ∈ Δs.SN (φ r) then Δs.PN (φ r) i a j * y r j else 0)
          atTop = liminf (fun r => Δs.PN (φ r) i a j * y r j) atTop := by
        refine Filter.liminf_congr ((hev j).mono fun r hr => ?_)
        rw [if_pos hr.2]
      rw [hc]
      have hPl : Tendsto (fun r => Δs.PN (φ r) i a j) atTop (𝓝 (M.P i a j)) :=
        (Δs.PN_lim i a (hmemA i) j).comp hφt
      rw [← hPl.liminf_eq]
      exact ENNReal.le_liminf_mul
    have hup : liminf (fun r => ENNReal.ofReal (M.C i a) + F r + ENNReal.ofReal K) atTop ≤
        ENNReal.ofReal (J0 + δ + K) + W i := by
      rw [← liminf_const_add atTop _ _ (by isBoundedDefault) (by isBoundedDefault)]
      exact liminf_le_liminf hstep
    exact hlow.trans hup
  -- convert to reals
  refine ⟨fun j => (W j).toReal - Q, fun j => by simp, fun i => ?_⟩
  set a := estar i
  have hPne : ∀ k, M.P i a k ≠ ⊤ := by
    intro k h
    have h2 : M.P i a k ≤ ∑' k, M.P i a k := ENNReal.le_tsum k
    rw [h, hM.2.2 i a (hmemA i)] at h2
    exact absurd h2 (by simp)
  have hfin : ∑' j, M.P i a j * W j ≠ ⊤ := by
    have := key i 1 one_pos
    intro h
    rw [h, add_top, top_add] at this
    exact absurd (top_le_iff.1 this) (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hWfin i⟩)
  have hsW : Summable (fun j => (M.P i a j).toReal * (W j).toReal) := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_mul] using this
  have hPsum : Summable (fun k => (M.P i a k).toReal) :=
    ENNReal.summable_toReal (by rw [hM.2.2 i a (hmemA i)]; simp)
  have hP1 : ∑' k, (M.P i a k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hPne, hM.2.2 i a (hmemA i)]; simp
  have hsw : Summable (fun j => (M.P i a j).toReal * ((W j).toReal - Q)) :=
    (hsW.sub (hPsum.mul_right Q)).congr (fun j => by ring)
  refine ⟨hsw, ?_⟩
  have htw : ∑' j, (M.P i a j).toReal * ((W j).toReal - Q) =
      ∑' j, (M.P i a j).toReal * (W j).toReal - Q := by
    have := hsW.tsum_sub (hPsum.mul_right Q)
    rw [tsum_mul_right, hP1, one_mul] at this
    rw [← this]; congr 1; funext j; ring
  have hTW : ∑' j, M.P i a j * W j = ENNReal.ofReal (∑' j, (M.P i a j).toReal * (W j).toReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) hsW]
    congr 1; funext j
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hPne j),
      ENNReal.ofReal_toReal (hWfin j)]
  have hC0 : 0 ≤ M.C i a := hM.2.1 i a (hmemA i)
  have hSW0 : 0 ≤ ∑' j, (M.P i a j).toReal * (W j).toReal :=
    tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hreal : ∀ δ : ℝ, 0 < δ → M.C i a + ∑' j, (M.P i a j).toReal * (W j).toReal ≤
      J0 + δ + (W i).toReal := by
    intro δ hδ
    have h := key i δ hδ
    have hJK : 0 ≤ J0 + δ + (|J0| + 1) := by have := neg_abs_le J0; linarith
    rw [hTW, ← ENNReal.ofReal_add hC0 hSW0, ← ENNReal.ofReal_add (add_nonneg hC0 hSW0)
      (by positivity), ← ENNReal.ofReal_toReal (hWfin i), ← ENNReal.ofReal_add hJK
      ENNReal.toReal_nonneg, ENNReal.ofReal_le_ofReal_iff (add_nonneg hJK ENNReal.toReal_nonneg)]
      at h
    linarith
  rw [htw]
  have : M.C i a + ∑' j, (M.P i a j).toReal * (W j).toReal ≤ J0 + (W i).toReal := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have := hreal (δ / 2) (by linarith); linarith
  linarith



/-- CT-B as in the plan (StrictMono). -/
theorem limit_acoi_ct {S Act : Type} [Countable S] {M : MDC S Act} (hM : M.IsValid)
    (Δs : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, -Q ≤ rN N i)
    (eN : ℕ → S → Act) (hmin : Δs.RealizesMin JN rN eN)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (estar : S → Act)
    (hlim : ∀ i, ∀ᶠ r in atTop, eN (φ r) i = estar i)
    (J0 : ℝ) (hJ : Tendsto (fun r => JN (φ r)) atTop (𝓝 J0)) :
    ∃ w : S → ℝ, (∀ i, -Q ≤ w i) ∧
      ∀ i, Summable (fun j => (M.P i (estar i) j).toReal * w j) ∧
        M.C i (estar i) + ∑' j, (M.P i (estar i) j).toReal * w j ≤ J0 + w i :=
  limit_acoi_ct' hM Δs JN rN hAC Q hQ0 hQ eN hmin φ hφ.tendsto_atTop estar hlim J0 hJ


lemma ofReal_step' (x y J : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ J + y) :
    ENNReal.ofReal x + ENNReal.ofReal (-J) ≤ ENNReal.ofReal J + ENNReal.ofReal y := by
  rcases le_or_gt 0 J with hJ | hJ
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -J ≤ 0), add_zero,
      ← ENNReal.ofReal_add hJ hy]
    exact ENNReal.ofReal_le_ofReal h
  · rw [ENNReal.ofReal_of_nonpos hJ.le, zero_add, ← ENNReal.ofReal_add hx (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

lemma lintegral_ofReal_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  have hE : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [hE, lintegral_withDensity_eq_lintegral_mul (μ := volume) (f := exponentialPDF r)
    (measurable_exponentialPDFReal r).ennreal_ofReal ENNReal.measurable_ofReal]
  have h1 : (exponentialPDF r * fun s => ENNReal.ofReal s) = Set.indicator (Set.Ioi 0)
      (fun s => ENNReal.ofReal (r * (s ^ ((2 : ℝ) - 1) * Real.exp (-(r * s))))) := by
    funext s
    simp only [Pi.mul_apply, exponentialPDF_eq]
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs), if_pos hs.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num
      ring
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ioi 0 from hs)]
      push_neg at hs
      rw [ENNReal.ofReal_of_nonpos hs]
      simp
  rw [h1, lintegral_indicator measurableSet_Ioi, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    congr 1
    rw [Real.rpow_two, Real.Gamma_two]
    field_simp
  · have h : IntegrableOn (fun x : ℝ => r * (x ^ (1 : ℝ) * Real.exp (-r * x ^ (1 : ℝ))))
        (Set.Ioi 0) := Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1)
          (p := 1) (b := r) (by norm_num) one_pos hr) r
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : (0 : ℝ) < s := hs
    positivity

/-- History-free expected sums under a stationary policy. -/
noncomputable def Est {S Act : Type} (Ψ : CTMDC S Act) (e : S → Act)
    (f : S → Act → ℝ → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n + 1, i => ∫⁻ s, f i (e i) s ∂(expMeasure (Ψ.ν i (e i))) +
      ∑' j, Ψ.P i (e i) j * Est Ψ e f n j

lemma expectedSum_stat {S Act : Type} (Ψ : CTMDC S Act) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (hν : ∀ i, 0 < Ψ.ν i (e i)) (f : S → Act → ℝ → ℝ≥0∞) :
    ∀ n k sa t i, CTMDC.expectedSum (Ψ.ofStationary e he) f n k sa t i = Est Ψ e f n i := by
  classical
  intro n
  induction n with
  | zero => intro k sa t i; simp [CTMDC.expectedSum, Est]
  | succ n ih =>
    intro k sa t i
    haveI := isProbabilityMeasure_expMeasure (hν i)
    simp only [CTMDC.expectedSum, Est, ih]
    simp only [CTMDC.ofStationary, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Ψ.A i) (e i), if_pos (he i),
      lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- CT-E (Lemma 10.3.1, p. 244). -/
theorem avgCost_le_of_ineq {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (Z : ℝ) (z : S → ℝ) (hz : BddBelow (Set.range z)) (h1015 : Ψ.Ineq1015 e Z z) :
    ∀ i, ((Ψ.avgCost (Ψ.ofStationary e he) i : ℝ≥0∞) : EReal) ≤ (Z : EReal) := by
  classical
  intro i0
  obtain ⟨htau, ⟨ε, hε, hε'⟩, -⟩ := hCTB
  obtain ⟨-, hpos, hP1, -⟩ := hΨ
  have hν : ∀ i, 0 < Ψ.ν i (e i) := fun i => (hpos i (e i) (he i)).2.2
  set τ : S → ℝ := fun i => Ψ.meanSojourn i (e i) with hτdef
  have hτ : ∀ i, τ i = 1 / Ψ.ν i (e i) := fun i => rfl
  have hτlow : ∀ i, tau + ε ≤ τ i := fun i => hε' i (e i) (he i)
  have hτ0 : ∀ i, 0 ≤ τ i := fun i => by have := hτlow i; linarith
  obtain ⟨m, hm⟩ := hz
  have hm' : ∀ k, m ≤ z k := fun k => hm ⟨k, rfl⟩
  set v : S → ℝ := fun k => z k - m with hv
  have hv0 : ∀ k, 0 ≤ v k := fun k => by simp [hv, hm' k]
  have hPne : ∀ j k, Ψ.P j (e j) k ≠ ⊤ := by
    intro j k h
    have h2 : Ψ.P j (e j) k ≤ ∑' k, Ψ.P j (e j) k := ENNReal.le_tsum k
    rw [h, hP1 j (e j) (he j)] at h2
    exact absurd h2 (by simp)
  have hPsum : ∀ j, Summable (fun k => (Ψ.P j (e j) k).toReal) := fun j =>
    ENNReal.summable_toReal (by rw [hP1 j (e j) (he j)]; simp)
  have hPR1 : ∀ j, ∑' k, (Ψ.P j (e j) k).toReal = 1 := by
    intro j
    rw [← ENNReal.tsum_toReal_eq (hPne j), hP1 j (e j) (he j)]; simp
  have hvsum : ∀ j, Summable (fun k => (Ψ.P j (e j) k).toReal * v k) := by
    intro j
    exact (((h1015 j).1).sub ((hPsum j).mul_right m)).congr (fun k => by simp [hv]; ring)
  have hvt : ∀ j, ∑' k, (Ψ.P j (e j) k).toReal * v k =
      ∑' k, (Ψ.P j (e j) k).toReal * z k - m := by
    intro j
    have := ((h1015 j).1).tsum_sub ((hPsum j).mul_right m)
    rw [tsum_mul_right, hPR1 j, one_mul] at this
    rw [← this]; congr 1; funext k; simp [hv]; ring
  have hPv : ∀ j, ∑' k, Ψ.P j (e j) k * ENNReal.ofReal (v k) =
      ENNReal.ofReal (∑' k, (Ψ.P j (e j) k).toReal * v k) := by
    intro j
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (hv0 k))
      (hvsum j)]
    congr 1; funext k
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hPne j k)]
  set c : S → ℝ := fun j => Ψ.G j (e j) + Ψ.g j (e j) * τ j with hcdef
  have hG0 : ∀ j, 0 ≤ Ψ.G j (e j) := fun j => (hpos j (e j) (he j)).1
  have hg0 : ∀ j, 0 ≤ Ψ.g j (e j) := fun j => (hpos j (e j) (he j)).2.1
  have hc0 : ∀ j, 0 ≤ c j := fun j => add_nonneg (hG0 j) (mul_nonneg (hg0 j) (hτ0 j))
  have hPv0 : ∀ j, 0 ≤ ∑' k, (Ψ.P j (e j) k).toReal * v k := fun j =>
    tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (hv0 k))
  set K := ENNReal.ofReal (-Z) with hK
  set Z' := ENNReal.ofReal Z with hZ'
  have hstep : ∀ j, ENNReal.ofReal (c j) + ∑' k, Ψ.P j (e j) k * ENNReal.ofReal (v k) +
      K * ENNReal.ofReal (τ j) ≤ Z' * ENNReal.ofReal (τ j) + ENNReal.ofReal (v j) := by
    intro j
    rw [hPv j, ← ENNReal.ofReal_add (hc0 j) (hPv0 j), hK, hZ',
      ← ENNReal.ofReal_mul' (hτ0 j), ← ENNReal.ofReal_mul' (hτ0 j),
      show -Z * τ j = -(Z * τ j) by ring]
    apply ofReal_step' _ _ _ (add_nonneg (hc0 j) (hPv0 j)) (hv0 j)
    rw [hvt j]
    have := (h1015 j).2
    simp only [hv, hcdef, hτdef] at this ⊢
    linarith
  -- the two expected sums
  set Ec := Est Ψ e Ψ.periodCost with hEc
  set Et := Est Ψ e (fun _ _ s => ENNReal.ofReal s) with hEt
  have hEc_succ : ∀ n j, Ec (n + 1) j = ENNReal.ofReal (c j) +
      ∑' k, Ψ.P j (e j) k * Ec n k := by
    intro n j
    haveI := isProbabilityMeasure_expMeasure (hν j)
    simp only [hEc, Est, CTMDC.periodCost]
    congr 1
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ ENNReal.measurable_ofReal, lintegral_ofReal_expMeasure (hν j),
      ← ENNReal.ofReal_mul (hg0 j), ← ENNReal.ofReal_add (hG0 j)
        (mul_nonneg (hg0 j) (one_div_pos.2 (hν j)).le)]
    rfl
  have hEt_succ : ∀ n j, Et (n + 1) j = ENNReal.ofReal (τ j) +
      ∑' k, Ψ.P j (e j) k * Et n k := by
    intro n j
    simp only [hEt, Est]
    rw [lintegral_ofReal_expMeasure (hν j)]
    rfl
  have hmain : ∀ n j, Ec n j + K * Et n j ≤ Z' * Et n j + ENNReal.ofReal (v j) := by
    intro n
    induction n with
    | zero => intro j; simp [hEc, hEt, Est]
    | succ n ih =>
      intro j
      have e1 : ∑' k, Ψ.P j (e j) k * (Ec n k + K * Et n k) =
          ∑' k, Ψ.P j (e j) k * Ec n k + K * ∑' k, Ψ.P j (e j) k * Et n k := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        congr 2; funext k; ring
      have e2 : ∑' k, Ψ.P j (e j) k * (Z' * Et n k + ENNReal.ofReal (v k)) =
          Z' * ∑' k, Ψ.P j (e j) k * Et n k +
            ∑' k, Ψ.P j (e j) k * ENNReal.ofReal (v k) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        congr 2; funext k; ring
      have hle : ∑' k, Ψ.P j (e j) k * (Ec n k + K * Et n k) ≤
          ∑' k, Ψ.P j (e j) k * (Z' * Et n k + ENNReal.ofReal (v k)) :=
        ENNReal.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (ih k) zero_le)
      rw [e1, e2] at hle
      rw [hEc_succ, hEt_succ]
      calc ENNReal.ofReal (c j) + ∑' k, Ψ.P j (e j) k * Ec n k +
            K * (ENNReal.ofReal (τ j) + ∑' k, Ψ.P j (e j) k * Et n k)
          = ENNReal.ofReal (c j) + K * ENNReal.ofReal (τ j) +
            (∑' k, Ψ.P j (e j) k * Ec n k + K * ∑' k, Ψ.P j (e j) k * Et n k) := by ring
        _ ≤ ENNReal.ofReal (c j) + K * ENNReal.ofReal (τ j) +
            (Z' * ∑' k, Ψ.P j (e j) k * Et n k +
              ∑' k, Ψ.P j (e j) k * ENNReal.ofReal (v k)) := add_le_add le_rfl hle
        _ = (ENNReal.ofReal (c j) + ∑' k, Ψ.P j (e j) k * ENNReal.ofReal (v k) +
              K * ENNReal.ofReal (τ j)) + Z' * ∑' k, Ψ.P j (e j) k * Et n k := by ring
        _ ≤ (Z' * ENNReal.ofReal (τ j) + ENNReal.ofReal (v j)) +
              Z' * ∑' k, Ψ.P j (e j) k * Et n k := add_le_add (hstep j) le_rfl
        _ = Z' * (ENNReal.ofReal (τ j) + ∑' k, Ψ.P j (e j) k * Et n k) +
              ENNReal.ofReal (v j) := by ring
  have hlow : ∀ (n : ℕ) j, (n : ℝ≥0∞) * ENNReal.ofReal (tau + ε) ≤ Et n j := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
      intro j
      rw [hEt_succ]
      have h2 : (n : ℝ≥0∞) * ENNReal.ofReal (tau + ε) ≤ ∑' k, Ψ.P j (e j) k * Et n k := by
        calc (n : ℝ≥0∞) * ENNReal.ofReal (tau + ε)
            = ∑' k, Ψ.P j (e j) k * ((n : ℝ≥0∞) * ENNReal.ofReal (tau + ε)) := by
              rw [ENNReal.tsum_mul_right, hP1 j (e j) (he j), one_mul]
          _ ≤ ∑' k, Ψ.P j (e j) k * Et n k :=
              ENNReal.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (ih k) zero_le)
      calc ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (tau + ε)
          = ENNReal.ofReal (tau + ε) + (n : ℝ≥0∞) * ENNReal.ofReal (tau + ε) := by
            push_cast; ring
        _ ≤ ENNReal.ofReal (τ j) + ∑' k, Ψ.P j (e j) k * Et n k :=
            add_le_add (ENNReal.ofReal_le_ofReal (hτlow j)) h2
  have hcostN : ∀ n, CTMDC.expCostN (Ψ.ofStationary e he) n i0 = Ec n i0 := fun n =>
    expectedSum_stat Ψ e he hν _ n 0 Fin.elim0 Fin.elim0 i0
  have htimeN : ∀ n, CTMDC.expTimeN (Ψ.ofStationary e he) n i0 = Et n i0 := fun n =>
    expectedSum_stat Ψ e he hν _ n 0 Fin.elim0 Fin.elim0 i0
  have hte : 0 < tau + ε := by linarith
  rcases lt_or_ge Z 0 with hZ | hZ
  · exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt (v i0 / (-Z * (tau + ε)))
    have h1 := hmain n i0
    rw [hZ', ENNReal.ofReal_of_nonpos hZ.le, zero_mul, zero_add] at h1
    have h2 : K * ((n : ℝ≥0∞) * ENNReal.ofReal (tau + ε)) ≤ ENNReal.ofReal (v i0) :=
      le_trans (mul_le_mul_of_nonneg_left (hlow n i0) zero_le) (le_trans le_add_self h1)
    rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_le_ofReal_iff (hv0 i0)] at h2
    rw [div_lt_iff₀ (by nlinarith)] at hn
    nlinarith
  · have hle : Ψ.avgCost (Ψ.ofStationary e he) i0 ≤ Z' := by
      unfold CTMDC.avgCost
      set X := ENNReal.ofReal (v i0 / (tau + ε)) with hX
      have hT : Tendsto (fun n : ℕ => Z' + X / n) atTop (𝓝 Z') := by
        have : Tendsto (fun n : ℕ => X * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (X * 0)) :=
          ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
            (Or.inr ENNReal.ofReal_ne_top)
        rw [mul_zero] at this
        simpa [div_eq_mul_inv] using tendsto_const_nhds.add this
      rw [← hT.limsup_eq]
      apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [hcostN, htimeN]
      apply ENNReal.div_le_of_le_mul
      have hXv : X / n * ((n : ℝ≥0∞) * ENNReal.ofReal (tau + ε)) = ENNReal.ofReal (v i0) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hn0 (ENNReal.natCast_ne_top n), hX,
          ← ENNReal.ofReal_mul (div_nonneg (hv0 i0) hte.le), div_mul_cancel₀ _ hte.ne']
      calc Ec n i0 ≤ Z' * Et n i0 + ENNReal.ofReal (v i0) :=
            le_trans le_self_add (hmain n i0)
        _ = Z' * Et n i0 + X / n * ((n : ℝ≥0∞) * ENNReal.ofReal (tau + ε)) := by rw [hXv]
        _ ≤ Z' * Et n i0 + X / n * Et n i0 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hlow n i0) zero_le)
        _ = (Z' + X / n) * Et n i0 := by ring
    calc ((Ψ.avgCost (Ψ.ofStationary e he) i0 : ℝ≥0∞) : EReal)
        ≤ ((Z' : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle
      _ = (Z : EReal) := by rw [hZ', EReal.coe_ennreal_ofReal, max_eq_left hZ]


/-- Lemma 10.3.2 (copied from our accepted proof b7dc0710). -/
theorem ineq_aux_iff' {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i) (Z : ℝ) :
    (∀ w : S → ℝ, Ψ.Ineq1020 tau e Z w → Ψ.Ineq1015 e Z (fun i => tau * w i)) ∧
      (∀ z : S → ℝ, Ψ.Ineq1015 e Z z → Ψ.Ineq1020 tau e Z (fun i => z i / tau)) := by
  classical
  obtain ⟨htau, ⟨ε, hε, hε'⟩, -⟩ := hCTB
  have hP0 := hΨ.2.2.2
  have hν : ∀ i, 0 < Ψ.ν i (e i) := by
    intro i
    have h := hε' i (e i) (he i)
    unfold CTMDC.meanSojourn at h
    have h1 : 0 < 1 / Ψ.ν i (e i) := by linarith
    simpa using h1
  have hlt : ∀ i, tau * Ψ.ν i (e i) < 1 := by
    intro i
    have h := hε' i (e i) (he i)
    unfold CTMDC.meanSojourn at h
    have h2 : tau < 1 / Ψ.ν i (e i) := by linarith
    rw [lt_div_iff₀ (hν i)] at h2
    exact h2
  have hdecomp : ∀ i (w : S → ℝ) j,
      ((Ψ.aux tau).P i (e i) j).toReal * w j =
        tau * Ψ.ν i (e i) * ((Ψ.P i (e i) j).toReal * w j) +
          (if j = i then (1 - tau * Ψ.ν i (e i)) * w i else 0) := by
    intro i w j
    simp only [CTMDC.aux]
    by_cases hj : j = i
    · subst hj
      have h1 : 0 ≤ 1 - tau * Ψ.ν j (e j) := by linarith [hlt j]
      simp [hP0 j (e j) (he j), ENNReal.toReal_ofReal h1]
    · have h1 : 0 ≤ tau * Ψ.ν i (e i) := (mul_pos htau (hν i)).le
      simp [hj, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1]
      ring
  have hsum : ∀ i (w : S → ℝ),
      Summable (fun j => ((Ψ.aux tau).P i (e i) j).toReal * w j) ↔
        Summable (fun j => (Ψ.P i (e i) j).toReal * w j) := by
    intro i w
    simp_rw [hdecomp i w]
    have hne : tau * Ψ.ν i (e i) ≠ 0 := (mul_pos htau (hν i)).ne'
    constructor
    · intro h
      have h2 := h.sub (hasSum_ite_eq i ((1 - tau * Ψ.ν i (e i)) * w i)).summable
      have h3 := h2.mul_left (tau * Ψ.ν i (e i))⁻¹
      refine h3.congr (fun j => ?_)
      simp only [add_sub_cancel_right]
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    · intro h
      exact (h.mul_left _).add (hasSum_ite_eq i _).summable
  have htsum : ∀ i (w : S → ℝ), Summable (fun j => (Ψ.P i (e i) j).toReal * w j) →
      ∑' j, ((Ψ.aux tau).P i (e i) j).toReal * w j =
        tau * Ψ.ν i (e i) * ∑' j, (Ψ.P i (e i) j).toReal * w j +
          (1 - tau * Ψ.ν i (e i)) * w i := by
    intro i w h
    simp_rw [hdecomp i w]
    rw [Summable.tsum_add (h.mul_left _) (hasSum_ite_eq i _).summable, tsum_mul_left,
      tsum_ite_eq]
  refine ⟨fun w hw i => ?_, fun z hz i => ?_⟩
  · obtain ⟨hs, hineq⟩ := hw i
    have hs' := (hsum i w).1 hs
    rw [htsum i w hs'] at hineq
    have hS : ∑' j, (Ψ.P i (e i) j).toReal * (tau * w j) =
        tau * ∑' j, (Ψ.P i (e i) j).toReal * w j := by
      rw [← tsum_mul_left]
      congr 1
      ext j
      ring
    refine ⟨(hs'.mul_left tau).congr (fun j => by ring), ?_⟩
    rw [hS]
    simp only [CTMDC.aux] at hineq
    unfold CTMDC.meanSojourn
    have hne : Ψ.ν i (e i) ≠ 0 := (hν i).ne'
    set ν := Ψ.ν i (e i)
    set Sw := ∑' j, (Ψ.P i (e i) j).toReal * w j
    have key : Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z - tau * ν * w i ≤ 0 := by
      linarith
    have heq : Z * (1 / ν) + tau * w i -
        (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + tau * Sw) =
        -(1 / ν) * (Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z - tau * ν * w i) := by
      field_simp
      ring
    have hpos : 0 ≤ -(1 / ν) * (Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z -
        tau * ν * w i) := by
      have : 0 < 1 / ν := one_div_pos.mpr (hν i)
      nlinarith
    linarith
  · obtain ⟨hs, hineq⟩ := hz i
    have hs' : Summable (fun j => (Ψ.P i (e i) j).toReal * (z j / tau)) :=
      (hs.mul_left tau⁻¹).congr (fun j => by ring)
    refine ⟨(hsum i _).2 hs', ?_⟩
    rw [htsum i _ hs']
    have hS : ∑' j, (Ψ.P i (e i) j).toReal * (z j / tau) =
        tau⁻¹ * ∑' j, (Ψ.P i (e i) j).toReal * z j := by
      rw [← tsum_mul_left]
      congr 1
      ext j
      ring
    rw [hS]
    simp only [CTMDC.aux]
    unfold CTMDC.meanSojourn at hineq
    have hne : Ψ.ν i (e i) ≠ 0 := (hν i).ne'
    have htne : tau ≠ 0 := htau.ne'
    set ν := Ψ.ν i (e i)
    set Sz := ∑' j, (Ψ.P i (e i) j).toReal * z j
    have key : 0 ≤ Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz) := by
      linarith
    have heq : Z + z i / tau -
        (Ψ.G i (e i) * ν + Ψ.g i (e i) + (tau * ν * (tau⁻¹ * Sz) + (1 - tau * ν) * (z i / tau))) =
        ν * (Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz)) := by
      field_simp
      ring
    have hpos : 0 ≤ ν * (Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz)) :=
      mul_nonneg (hν i).le key
    linarith

/-- The parent (Theorem 10.3.3, corrected). -/
theorem main {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := hQ
  have hM := aux_isValid Ψ hΨ tau B hCTB
  -- limit policies: membership, aux bound and (10.20)
  have hpol : ∀ (eN : ℕ → S → Act), Δs.RealizesMin JN rN eN → ∀ φ : ℕ → ℕ,
      Tendsto φ atTop atTop → ∀ estar : S → Act, (∀ i, ∀ᶠ r in atTop, eN (φ r) i = estar i) →
      ∀ J0 : ℝ, Tendsto (fun r => JN (φ r)) atTop (𝓝 J0) →
      ∃ he : ∀ i, estar i ∈ Ψ.A i, ∃ w : S → ℝ, (∀ i, -Q ≤ w i) ∧
        (∀ i, (((Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i : ℝ≥0∞) : EReal) ≤
          (J0 : EReal)) ∧ Ψ.Ineq1020 tau estar J0 w := by
    intro eN hmin φ hφ estar hlim J0 hJ
    have he : ∀ i, estar i ∈ Ψ.A i := by
      intro i
      obtain ⟨N₁, h1, h2⟩ := Δs.SN_cover i
      obtain ⟨r, hr1, hr2⟩ := ((hφ.eventually (eventually_ge_atTop N₁)).and (hlim i)).exists
      rw [← hr2]
      exact (hmin (φ r) (h1.trans hr1) i (Δs.SN_mono N₁ (φ r) h1 hr1 h2)).1
    obtain ⟨w, hw, hacoi⟩ :=
      limit_acoi_ct' hM Δs JN rN hAC Q hQ0 hQ eN hmin φ hφ estar hlim J0 hJ
    have hbdd : BddBelow (Set.range w) := ⟨-Q, by rintro _ ⟨i, rfl⟩; exact hw i⟩
    exact ⟨he, w, hw, avgCost_le_of_acoi (Ψ.aux tau) hM estar he J0 w hbdd
      (fun i => (hacoi i).1) (fun i => (hacoi i).2), fun i => hacoi i⟩
  -- a minimizing sequence
  have hex : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N,
      ∃ a ∈ Ψ.A i, JN N + rN N i = Δs.bracket N (rN N) i a := by
    intro N hN i hi
    obtain ⟨hA, heq⟩ := hAC.1 N hN i hi
    obtain ⟨a, ha, h⟩ := Finset.exists_mem_eq_inf' hA (fun a => Δs.bracket N (rN N) i a)
    exact ⟨a, ha, heq.trans h⟩
  let e0 : ℕ → S → Act := fun N i =>
    if h : ∃ a ∈ Ψ.A i, JN N + rN N i = Δs.bracket N (rN N) i a then h.choose
    else (hΨ.1 i).choose
  have he0 : Δs.RealizesMin JN rN e0 := by
    intro N hN i hi
    have h := hex N hN i hi
    simp only [e0, dif_pos h]
    exact h.choose_spec
  -- every convergent subsequence of JN converges to the aux value
  have hsub : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ J0 : ℝ,
      Tendsto (fun r => JN (φ r)) atTop (𝓝 J0) →
      ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (J0 : EReal) := by
    intro φ hφ J0 hJ i
    obtain ⟨ψ, hψ, e', -, hlim'⟩ :=
      exists_subseq_limit_ct' Δs e0 (fun N hN i hi => (he0 N hN i hi).1) φ hφ
    obtain ⟨he, w, hw, hle, -⟩ := hpol e0 he0 (φ ∘ ψ) (hφ.comp hψ.tendsto_atTop) e' hlim' J0
      (hJ.comp hψ.tendsto_atTop)
    apply le_antisymm
    · exact (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le _ _)).trans (hle i)
    · have h1 : Tendsto (fun r => ((JN (φ r) : ℝ) : EReal)) atTop (𝓝 (J0 : EReal)) :=
        (continuous_coe_real_ereal.tendsto _).comp hJ
      calc (J0 : EReal) = limsup (fun r => ((JN (φ r) : ℝ) : EReal)) atTop := h1.limsup_eq.symm
        _ = limsup ((fun N => ((JN N : ℝ) : EReal)) ∘ φ) atTop := rfl
        _ ≤ limsup (fun N => ((JN N : ℝ) : EReal)) atTop := by
            rw [limsup_comp]
            exact limsup_le_limsup_of_le hφ
        _ ≤ _ := hAC.2.2.2.2 i
  -- bounds on JN
  obtain ⟨i0, -⟩ := Δs.SN_nonempty Δs.N0 le_rfl
  obtain ⟨U, hU⟩ : ∃ U : ℝ, ∀ᶠ N in atTop, JN N ≤ U := by
    obtain ⟨U, hU1, -⟩ := EReal.lt_iff_exists_real_btwn.1 hAC.2.2.2.1
    exact ⟨U, (eventually_lt_of_limsup_lt hU1).mono fun N hN => (EReal.coe_lt_coe_iff.1 hN).le⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ℝ, ∀ᶠ N in atTop, rN N i0 ≤ U' := by
    obtain ⟨U, hU1, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hAC.2.1 i0)
    exact ⟨U, (eventually_lt_of_limsup_lt hU1).mono fun N hN => (EReal.coe_lt_coe_iff.1 hN).le⟩
  have hJlow : ∀ᶠ N in atTop, -Q - U' ≤ JN N := by
    obtain ⟨N₁, h1, h2⟩ := Δs.SN_cover i0
    filter_upwards [eventually_ge_atTop N₁, hU'] with N hN hr
    have hN0 : Δs.N0 ≤ N := h1.trans hN
    have hi : i0 ∈ Δs.SN N := Δs.SN_mono N₁ N h1 hN h2
    obtain ⟨hmem, heq⟩ := he0 N hN0 i0 hi
    unfold ApproxSeq.bracket at heq
    have hsum1 := Δs.PN_sum N hN0 i0 hi (e0 N i0) hmem
    have hPNne : ∀ j ∈ Δs.SN N, Δs.PN N i0 (e0 N i0) j ≠ ⊤ := by
      intro j hj h
      have : Δs.PN N i0 (e0 N i0) j ≤ ∑ k ∈ Δs.SN N, Δs.PN N i0 (e0 N i0) k :=
        Finset.single_le_sum (fun _ _ => zero_le) hj
      rw [h, hsum1] at this
      exact absurd this (by simp)
    have hsumR : ∑ j ∈ Δs.SN N, (Δs.PN N i0 (e0 N i0) j).toReal = 1 := by
      rw [← ENNReal.toReal_sum hPNne, hsum1]; simp
    have hC0 : 0 ≤ (Ψ.aux tau).C i0 (e0 N i0) := hM.2.1 i0 _ hmem
    have hge : -Q ≤ ∑ j ∈ Δs.SN N, (Δs.PN N i0 (e0 N i0) j).toReal * rN N j := by
      calc -Q = ∑ j ∈ Δs.SN N, (Δs.PN N i0 (e0 N i0) j).toReal * (-Q) := by
            rw [← Finset.sum_mul, hsumR, one_mul]
        _ ≤ _ := Finset.sum_le_sum (fun j hj =>
            mul_le_mul_of_nonneg_left (hQ N hN0 j hj) ENNReal.toReal_nonneg)
    linarith
  have hbd : ∀ᶠ N in atTop, JN N ∈ Set.Icc (-Q - U') U :=
    (hJlow.and hU).mono fun N h => ⟨h.1, h.2⟩
  set V : ℝ := (((Ψ.aux tau).avgValue i0 : ℝ≥0∞) : EReal).toReal with hV
  have hconv : Tendsto JN atTop (𝓝 V) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨a, -, ms, hms, hlim⟩ := tendsto_subseq_of_frequently_bounded
      (Metric.isBounded_Icc (-Q - U') U) (hns.eventually hbd).frequently
    refine ⟨ms, ?_⟩
    have h := hsub (ns ∘ ms) (hns.comp hms.tendsto_atTop) a hlim i0
    have haV : a = V := by rw [hV, h, EReal.toReal_coe]
    rw [← haV]
    exact hlim
  have hval : ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (V : EReal) :=
    hsub id tendsto_id V hconv
  -- the policy part
  have hfull : ∀ (eN : ℕ → S → Act), Δs.RealizesMin JN rN eN → ∀ φ : ℕ → ℕ,
      Tendsto φ atTop atTop → ∀ estar : S → Act, (∀ i, ∀ᶠ r in atTop, eN (φ r) i = estar i) →
      ∃ he : ∀ i, estar i ∈ Ψ.A i,
        (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
          (Ψ.aux tau).avgValue i) ∧
        (∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i) ∧
        ∀ i, ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (V : EReal) := by
    intro eN hmin φ hφ estar hlim
    obtain ⟨he, w, hw, hle, h1020⟩ := hpol eN hmin φ hφ estar hlim V (hconv.comp hφ)
    have h1015 := (ineq_aux_iff' Ψ hΨ tau B hCTB estar he V).1 w h1020
    have htau := hCTB.1
    have hbdd : BddBelow (Set.range (fun i => tau * w i)) :=
      ⟨-(tau * Q), by rintro _ ⟨i, rfl⟩; have := hw i; nlinarith⟩
    have hΨle := avgCost_le_of_ineq Ψ hΨ tau B hCTB estar he V (fun i => tau * w i) hbdd h1015
    refine ⟨he, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · apply le_antisymm
      · exact EReal.coe_ennreal_le_coe_ennreal_iff.1 ((hle i).trans (hval i).ge)
      · exact iInf_le _ _
    · apply le_antisymm
      · exact EReal.coe_ennreal_le_coe_ennreal_iff.1 ((hΨle i).trans
          ((hval i).ge.trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hCTAC i))))
      · exact iInf_le _ _
    · apply le_antisymm
      · exact (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le _ _)).trans (hΨle i)
      · exact (hval i).ge.trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hCTAC i))
  refine ⟨⟨V, hconv, fun i => ⟨hval i, ?_⟩⟩, ?_⟩
  · obtain ⟨ψ, hψ, e', -, hlim'⟩ :=
      exists_subseq_limit_ct' Δs e0 (fun N hN i hi => (he0 N hN i hi).1) id tendsto_id
    obtain ⟨-, -, -, h⟩ := hfull e0 he0 ψ hψ.tendsto_atTop e' hlim'
    exact h i
  · rintro eN estar hmin ⟨φ, hφ, -, hlim⟩
    obtain ⟨he, h1, h2, -⟩ := hfull eN hmin φ hφ.tendsto_atTop estar hlim
    exact ⟨he, h1, h2⟩

end SennottDP.ContinuousTime.Ebeb

open Filter Topology SennottDP.ContinuousTime in open scoped ENNReal in
theorem solution {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i := by
  exact SennottDP.ContinuousTime.Ebeb.main Ψ hΨ tau B hCTB hCTAC Δs JN rN hAC hQ
