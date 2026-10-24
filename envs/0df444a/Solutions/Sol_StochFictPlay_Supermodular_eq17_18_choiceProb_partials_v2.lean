-- Prove2me | solution 1 for StochFictPlay.Supermodular.eq17_18_choiceProb_partials_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:21:53.672982+00:00
-- url     : https://prove2.me/submissions/15e496f1-1a77-414a-864a-6b57d077b798

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel_v2

open MeasureTheory
open scoped ENNReal

namespace SF90
open StochFictPlay.Supermodular

theorem line_deriv {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π v : Fin m → ℝ)
    (i : Fin m) :
    HasDerivAt (fun t : ℝ => choiceProb f (π + t • v) i) (fderiv ℝ (choiceProb f) π v i) 0 := by
  have hd : Differentiable ℝ (choiceProb f) := hf.2.2.2.2.differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => π + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add π
  have hC : HasFDerivAt (choiceProb f) (fderiv ℝ (choiceProb f) π) (π + (0:ℝ) • v) := by
    simpa using (hd π).hasFDerivAt
  have := hC.comp_hasDerivAt (0:ℝ) h1
  exact hasDerivAt_pi.1 this i

theorem shift_inv {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) (t : ℝ) :
    choiceProb f (π + t • (1 : Fin m → ℝ)) = choiceProb f π := by
  funext i
  unfold choiceProb
  congr 2
  ext e
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  constructor
  · intro h j hj; have := h j hj; linarith
  · intro h j hj; have := h j hj; linarith

theorem row_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i : Fin m) : ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 := by
  have h := line_deriv f hf π 1 i
  simp only [shift_inv] at h
  have h0 := h.unique (hasDerivAt_const (0:ℝ) (choiceProb f π i))
  rw [← Finset.sum_apply, ← map_sum]
  have : ∑ j : Fin m, Pi.single j (1:ℝ) = (1 : Fin m → ℝ) :=
    Finset.univ_sum_single (fun _ : Fin m => (1:ℝ))
  rw [this, h0]

theorem split_sum {m : ℕ} (g : Fin m → ℝ) (p : Fin m → Prop) [DecidablePred p] :
    ∑ j, (if p j then g j else 0) = ∑ j, g j + ∑ j, (if ¬ p j then -g j else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p j <;> simp [h]

theorem combin {m : ℕ} (D : Fin m → Fin m → ℝ) (hr : ∀ i, ∑ j, D i j = 0)
    (hc : ∀ j, ∑ i, D i j = 0) (hn : ∀ i j, i ≠ j → D i j < 0) (k l : Fin m)
    (hk : k.val + 1 < m) (hl : l.val + 1 < m) :
    0 < ∑ i : Fin m, ∑ j : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0) := by
  have hm : 0 < m := by omega
  let last : Fin m := ⟨m - 1, by omega⟩
  let zero : Fin m := ⟨0, hm⟩
  have hlastk : ¬ last ≤ k := by simp only [Fin.le_def, last]; omega
  have hlastl : ¬ last ≤ l := by simp only [Fin.le_def, last]; omega
  have hzk : zero ≤ k := by simp [Fin.le_def, zero]
  have hzl : zero ≤ l := by simp [Fin.le_def, zero]
  rcases le_or_gt k l with hkl | hkl
  · have e1 : ∀ i, ∑ j : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0)
        = ∑ j : Fin m, (if i ≤ k ∧ ¬ j ≤ l then -D i j else 0) := by
      intro i
      by_cases hi : i ≤ k
      · simp only [hi, true_and]
        rw [split_sum (D i) (fun j => j ≤ l), hr i, zero_add]
      · simp [hi]
    simp_rw [e1]
    have hnn : ∀ i j, 0 ≤ (if i ≤ k ∧ ¬ j ≤ l then -D i j else 0) := by
      intro i j
      split_ifs with h
      · have : i ≠ j := by
          intro e; subst e; exact h.2 (h.1.trans hkl)
        linarith [hn i j this]
      · rfl
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
    refine ⟨zero, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ => hnn zero j)
    refine ⟨last, Finset.mem_univ _, ?_⟩
    rw [if_pos ⟨hzk, hlastl⟩]
    have : zero ≠ last := fun e => hlastk (e ▸ hzk)
    linarith [hn zero last this]
  · rw [Finset.sum_comm]
    have e1 : ∀ j, ∑ i : Fin m, (if i ≤ k ∧ j ≤ l then D i j else 0)
        = ∑ i : Fin m, (if ¬ i ≤ k ∧ j ≤ l then -D i j else 0) := by
      intro j
      by_cases hj : j ≤ l
      · simp only [hj, and_true]
        rw [split_sum (fun i => D i j) (fun i => i ≤ k), hc j, zero_add]
      · simp [hj]
    simp_rw [e1]
    have hnn : ∀ j i, 0 ≤ (if ¬ i ≤ k ∧ j ≤ l then -D i j else 0) := by
      intro j i
      split_ifs with h
      · have : i ≠ j := by
          intro e; subst e; exact h.1 (h.2.trans hkl.le)
        linarith [hn i j this]
      · rfl
    apply Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun i _ => hnn j i)
    refine ⟨zero, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun i _ => hnn zero i)
    refine ⟨last, Finset.mem_univ _, ?_⟩
    rw [if_pos ⟨hlastk, hzl⟩]
    have : last ≠ zero := fun e => hlastk (e ▸ hzk)
    linarith [hn last zero this]


theorem tie_null {m : ℕ} (a b : Fin m) (hab : a ≠ b) (c : ℝ) :
    volume {e : Fin m → ℝ | e a = e b + c} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) a -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) b
  have hL : ∀ x, L x = x a - x b := fun x => rfl
  let p : Fin m → ℝ := c • Pi.single a 1
  have hp : L p = c := by simp [hL, p, hab.symm]
  let s : AffineSubspace ℝ (Fin m → ℝ) := AffineSubspace.mk' p (LinearMap.ker L)
  have hsub : {e : Fin m → ℝ | e a = e b + c} ⊆ s := by
    intro e he
    simp only [Set.mem_ofPred_eq] at he
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hp, hL]
    linarith
  have hne : s ≠ ⊤ := by
    intro h
    have hq : p + Pi.single a 1 ∈ s := by rw [h]; exact AffineSubspace.mem_top _ _ _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, add_sub_cancel_left, hL] at hq
    simp [hab.symm] at hq
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace _ s hne)

theorem meas_E {m : ℕ} (π : Fin m → ℝ) (i : Fin m) :
    MeasurableSet {e : Fin m → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i} := by
  have : {e : Fin m → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i}
      = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin m → ℝ | π j + e j < π i + e i} := by
    ext e; simp
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem mu_univ {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) :
    (volume.withDensity f) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf.2.2.2.1]

theorem sum_one {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (hm : Nonempty (Fin m)) :
    ∑ i, choiceProb f π i = 1 := by
  set μ := volume.withDensity f
  set E : Fin m → Set (Fin m → ℝ) := fun i => {e | ∀ j, j ≠ i → π j + e j < π i + e i}
  have hU : μ Set.univ = 1 := mu_univ f hf
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i i' hii'
    refine Set.disjoint_left.2 fun e h1 h2 => ?_
    have := h1 i' (Ne.symm hii'); have := h2 i hii'; linarith
  have hunion : μ (⋃ i, E i) = ∑ i, μ (E i) := by
    rw [measure_iUnion hdisj (fun i => meas_E π i), tsum_fintype]
  have hcompl : μ (⋃ i, E i)ᶜ = 0 := by
    have hsub : (⋃ i, E i)ᶜ ⊆ ⋃ a, ⋃ b, ⋃ (_ : a ≠ b), {e : Fin m → ℝ | e a = e b + (π b - π a)} := by
      intro e he
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at he
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => π k + e k) hne
      have := he i
      simp only [E, Set.mem_ofPred_eq, not_forall, not_lt] at this
      obtain ⟨j, hji, hj⟩ := this
      have := hi j (Finset.mem_univ _)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨j, i, hji, by linarith⟩
    refine measure_mono_null hsub ?_
    refine (measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null fun hab => ?_)
    exact withDensity_absolutelyContinuous _ _ (tie_null a b hab _)
  have hfull : μ (⋃ i, E i) = 1 := by
    apply le_antisymm (hU ▸ measure_mono (Set.subset_univ _))
    calc (1 : ℝ≥0∞) = μ Set.univ := hU.symm
      _ ≤ μ ((⋃ i, E i) ∪ (⋃ i, E i)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ (⋃ i, E i) + μ (⋃ i, E i)ᶜ := measure_union_le _ _
      _ = μ (⋃ i, E i) := by rw [hcompl, add_zero]
  have hfin : ∀ i, μ (E i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [hU]; exact ENNReal.one_ne_top) (measure_mono (Set.subset_univ _))
  unfold choiceProb
  change ∑ i, (μ (E i)).toReal = 1
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hunion, hfull, ENNReal.toReal_one]

theorem col_sum {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (j : Fin m) : ∑ i : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0 := by
  have hm : Nonempty (Fin m) := ⟨j⟩
  have h : HasDerivAt (fun t : ℝ => ∑ i, choiceProb f (π + t • Pi.single j (1:ℝ)) i)
      (∑ i : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i) 0 :=
    HasDerivAt.fun_sum (fun i _ => line_deriv f hf π _ i)
  simp only [sum_one f hf _ hm] at h
  exact h.unique (hasDerivAt_const (0:ℝ) (1:ℝ))


theorem pfsa_apply {n : ℕ} (i : Fin (n+1)) (e : Fin (n+1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i e = (e i, fun k => e (i.succAbove k)) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]; rfl

theorem region_bound {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hfc : Continuous f)
    (hpos : ∀ e, 0 < f e) (hfin : ∀ e, f e ≠ ⊤) (π : Fin (n+1) → ℝ) (i j : Fin (n+1))
    (hij : i ≠ j) :
    ∃ c > 0, ∃ r > 0, ∀ t : ℝ, 0 < t → t < r → ∃ R : Set (Fin (n+1) → ℝ),
      R ⊆ {e | (∀ k, k ≠ i → π k + e k < π i + e i) ∧ π i + e i ≤ π j + t + e j} ∧
      ENNReal.ofReal (c * t) ≤ volume.withDensity f R := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  set e0 : Fin (n+1) → ℝ := fun k => if k = i then 0 else if k = j then π i - π j
    else π i - π k - 1 with he0
  have e0i : e0 i = 0 := by simp [he0]
  have e0j : e0 j = π i - π j := by simp [he0, hij.symm]
  have e0k : ∀ k, k ≠ i → k ≠ j → e0 k = π i - π k - 1 := by
    intro k h1 h2; simp [he0, h1, h2]
  set δ := f e0 / 2 with hδ
  have hδpos : 0 < δ := ENNReal.half_pos (hpos e0).ne'
  have hδlt : δ < f e0 := ENNReal.half_lt_self (hpos e0).ne' (hfin e0)
  have hδfin : δ ≠ ⊤ := ne_top_of_lt hδlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((hfc.tendsto e0).eventually (lt_mem_nhds hδlt))
  set r := min (ε / 2) (1 / 4) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r ≤ ε / 2 := min_le_left _ _
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  set B : Set (Fin n → ℝ) := Set.univ.pi fun k' => Set.Ioo (e0 (i.succAbove k') - r) (e0 (i.succAbove k') + r)
    with hB
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  set V := (volume : Measure (Fin n → ℝ)) B with hV
  have hVeq : V = ∏ _k' : Fin n, ENNReal.ofReal (2 * r) := by
    rw [hV, hB, Real.volume_pi_Ioo]; congr 1; ext k'; congr 1; ring
  have hVpos : V ≠ 0 := by
    rw [hVeq, Finset.prod_ne_zero_iff]; intro _ _; simp; linarith
  have hVfin : V ≠ ⊤ := by rw [hVeq]; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  refine ⟨(δ * V).toReal, ENNReal.toReal_pos (mul_ne_zero hδpos.ne' hVpos)
    (ENNReal.mul_ne_top hδfin hVfin), r, hr0, fun t ht htr => ?_⟩
  set W : Set (ℝ × (Fin n → ℝ)) := {p | p.2 ∈ B ∧ p.1 ∈ Set.Ioc (π j + p.2 j' - π i) (π j + p.2 j' - π i + t)}
    with hW
  have hWm : MeasurableSet W := by
    have : W = Prod.snd ⁻¹' B ∩ ({p : ℝ × (Fin n → ℝ) | π j + p.2 j' - π i < p.1} ∩
        {p : ℝ × (Fin n → ℝ) | p.1 ≤ π j + p.2 j' - π i + t}) := by
      ext p; simp [hW]
    rw [this]
    refine (measurable_snd hBm).inter ?_
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  set R := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' W with hRdef
  have memR : ∀ e ∈ R, (∀ k', e (i.succAbove k') ∈ Set.Ioo (e0 (i.succAbove k') - r) (e0 (i.succAbove k') + r))
      ∧ π j + e j - π i < e i ∧ e i ≤ π j + e j - π i + t := by
    intro e he
    simp only [hRdef, Set.mem_preimage, pfsa_apply, hW, hB, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Ioc] at he
    rw [hj'] at he
    exact ⟨he.1, he.2.1, he.2.2⟩
  -- bounds on e i
  have bnd : ∀ e ∈ R, -r < e i ∧ e i < 2 * r := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := memR e he
    have := h1 j'
    rw [hj', e0j] at this
    constructor <;> [linarith [this.1]; linarith [this.2]]
  refine ⟨R, ?_, ?_⟩
  · intro e he
    obtain ⟨h1, h2, h3⟩ := memR e he
    obtain ⟨b1, b2⟩ := bnd e he
    refine ⟨fun k hk => ?_, by linarith⟩
    obtain ⟨k', rfl⟩ | h := (Fin.eq_self_or_eq_succAbove i k).symm.imp id id
    · by_cases hkj : i.succAbove k' = j
      · rw [hkj]; linarith
      · have := (h1 k').2
        rw [e0k _ hk hkj] at this
        linarith
    · exact absurd h hk
  · -- measure
    have hvolR : volume R = ENNReal.ofReal t * V := by
      change (Measure.pi fun _ => volume) _ = _
      rw [hRdef, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) i).measure_preimage
        hWm.nullMeasurableSet, Measure.prod_apply_symm hWm]
      have : ∀ y : Fin n → ℝ, volume ((fun x : ℝ => (x, y)) ⁻¹' W) = B.indicator (fun _ => ENNReal.ofReal t) y := by
        intro y
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          have : (fun x : ℝ => (x, y)) ⁻¹' W = Set.Ioc (π j + y j' - π i) (π j + y j' - π i + t) := by
            ext x; simp [hW, hy]
          rw [this, Real.volume_Ioc]; congr 1; ring
        · rw [Set.indicator_of_notMem hy]
          have : (fun x : ℝ => (x, y)) ⁻¹' W = ∅ := by
            ext x; simp [hW, hy]
          rw [this, measure_empty]
      simp_rw [this]
      rw [lintegral_indicator_const hBm]
      rfl
    have hRm : MeasurableSet R := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).measurable hWm
    have hlow : δ * (ENNReal.ofReal t * V) ≤ volume.withDensity f R := by
      rw [withDensity_apply _ hRm, ← hvolR, ← setLIntegral_const]
      apply setLIntegral_mono hfc.measurable
      intro e he
      apply le_of_lt
      apply hball
      rw [dist_pi_lt_iff hε]
      intro k
      rw [Real.dist_eq]
      obtain ⟨b1, b2⟩ := bnd e he
      obtain ⟨h1, -, -⟩ := memR e he
      rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k', rfl⟩
      · rw [e0i, sub_zero, abs_lt]; constructor <;> linarith
      · have := h1 k'
        rw [abs_lt]; constructor <;> linarith [this.1, this.2]
    calc ENNReal.ofReal ((δ * V).toReal * t) = δ * (ENNReal.ofReal t * V) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
            (ENNReal.mul_ne_top hδfin hVfin)]
          ring
      _ ≤ _ := hlow

theorem offdiag_neg {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i j : Fin m) (hij : i ≠ j) : fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i < 0 := by
  have hd := line_deriv f hf π (Pi.single j (1:ℝ)) i
  set d := fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i
  cases m with
  | zero => exact i.elim0
  | succ n =>
  obtain ⟨c, hc, r, hr, H⟩ := region_bound f hf.1 hf.2.1 hf.2.2.1 π i j hij
  set g := fun t : ℝ => choiceProb f (π + t • Pi.single j (1:ℝ)) i
  have key : ∀ t, 0 < t → t < r → g t ≤ g 0 - c * t := by
    intro t ht htr
    obtain ⟨R, hRsub, hRlow⟩ := H t ht htr
    set μ := volume.withDensity f
    set E := {e : Fin (n+1) → ℝ | ∀ k, k ≠ i → π k + e k < π i + e i}
    set π' := π + t • Pi.single j (1:ℝ)
    set E' := {e : Fin (n+1) → ℝ | ∀ k, k ≠ i → π' k + e k < π' i + e i}
    have hπ'i : π' i = π i := by simp [π', hij]
    have hπ'j : π' j = π j + t := by simp [π']
    have hπ'le : ∀ k, π k ≤ π' k := by
      intro k; simp only [π', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (0:ℝ) ≤ (Pi.single j (1:ℝ) : Fin (n+1) → ℝ) k := by
        by_cases h : k = j
        · subst h; simp
        · simp [h]
      nlinarith
    have hsub : E' ⊆ E := by
      intro e he k hk
      have := he k hk; have := hπ'le k; rw [hπ'i] at *; linarith
    have hRdiff : R ⊆ E \ E' := by
      intro e he
      obtain ⟨h1, h2⟩ := hRsub he
      refine ⟨h1, fun h' => ?_⟩
      have := h' j hij.symm
      rw [hπ'i, hπ'j] at this
      linarith
    have hU : μ Set.univ = 1 := mu_univ f hf
    have hfin : ∀ s, μ s ≠ ⊤ := fun s =>
      ne_top_of_le_ne_top (by rw [hU]; exact ENNReal.one_ne_top) (measure_mono (Set.subset_univ _))
    have hsplit : μ E' + μ (E \ E') = μ E := by
      rw [measure_add_sdiff (meas_E π' i).nullMeasurableSet, Set.union_eq_right.2 hsub]
    have hg0 : g 0 = (μ E).toReal := by simp [g, choiceProb, μ, E]
    have hgt : g t = (μ E').toReal := rfl
    rw [hg0, hgt, ← hsplit, ENNReal.toReal_add (hfin _) (hfin _)]
    have : c * t ≤ (μ (E \ E')).toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfin _)).2
        (hRlow.trans (measure_mono hRdiff))
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  have hlim := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t⁻¹ • (g (0 + t) - g 0) ≤ -c := by
    have : Set.Ioo (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hr
    filter_upwards [this] with t ht
    obtain ⟨ht0, htr⟩ := ht
    rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ ht0]
    have := key t ht0 htr
    nlinarith
  have := le_of_tendsto hlim hev
  linarith

end SF90

open StochFictPlay.Supermodular in
theorem solution (m : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin m → ℝ) :
    (∀ k l : Fin m, k.val + 1 < m → l.val + 1 < m →
      0 < ∑ i : Fin m, ∑ j : Fin m,
        (if i ≤ k ∧ j ≤ l then fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i else 0)) ∧
    (∀ i : Fin m, ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0) :=
  ⟨fun k l hk hl => SF90.combin (fun i j => fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i)
      (SF90.row_sum f hf π) (SF90.col_sum f hf π) (fun i j h => SF90.offdiag_neg f hf π i j h)
      k l hk hl,
    SF90.row_sum f hf π⟩
