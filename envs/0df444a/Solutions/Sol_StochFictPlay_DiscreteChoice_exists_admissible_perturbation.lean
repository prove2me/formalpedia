-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.exists_admissible_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:50:59.26707+00:00
-- url     : https://prove2.me/submissions/fe68b89b-578b-4b69-8671-8196e29a590b

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel_v2
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex
import Definitions.Def_StochFictPlay_DiscreteChoice_Admissible

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS.AuxD555

open StochFictPlay.ZeroSumESS

/-- the event that alternative `i` is the strict argmax of `π + e` -/
def Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  {e | ∀ j, j ≠ i → π j + e j < π i + e i}

noncomputable abbrev μf {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) : Measure (Fin m → ℝ) :=
  (volume : Measure (Fin m → ℝ)).withDensity f

theorem choiceProb_eq {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) (i : Fin m) :
    choiceProb f π i = (μf f).real (Ev π i) := rfl

theorem tie_null {n : ℕ} (j k : Fin n) (hjk : k ≠ j) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {e | e k - e j = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : ∀ e, L e = e k - e j := fun e => rfl
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at hmem
    simp [Ne.symm hjk] at hmem
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) _ hne
  have hset : {e : Fin n → ℝ | e k - e j = c} =
      (fun e => e + (-(c • Pi.single k (1:ℝ)))) ⁻¹' (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hL]
    simp [Ne.symm hjk]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact h0

theorem measurableSet_Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : MeasurableSet (Ev π i) := by
  have hAi : Ev π i = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin m → ℝ | π j + e j < π i + e i} := by
    ext e; simp [Ev]
  rw [hAi]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem isOpen_Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : IsOpen (Ev π i) := by
  have : Ev π i = ⋂ j, {e : Fin m → ℝ | j ≠ i → π j + e j < π i + e i} := by
    ext e; simp [Ev]
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases h : j = i
  · simp [h]
  · simpa [h] using isOpen_lt (by fun_prop : Continuous fun e : Fin m → ℝ => π j + e j)
      (by fun_prop : Continuous fun e : Fin m → ℝ => π i + e i)

theorem Ev_nonempty {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : (Ev π i).Nonempty := by
  refine ⟨fun j => -π j + if j = i then 1 else 0, ?_⟩
  intro j hj
  simp [hj]

theorem Ev_disjoint {m : ℕ} (π : Fin m → ℝ) {a b : Fin m} (hab : a ≠ b) (e : Fin m → ℝ)
    (ha : e ∈ Ev π a) (hb : e ∈ Ev π b) : False := by
  have h1 := ha b (Ne.symm hab)
  have h2 := hb a hab
  linarith

variable {m : ℕ} {f : (Fin m → ℝ) → ℝ≥0∞}

theorem isProb (hf : IsRegularDensity f) : IsProbabilityMeasure (μf f) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hf.2.2.2.1

theorem mu_pos (hf : IsRegularDensity f) {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μf f U := by
  have hfm : Measurable f := hf.1.measurable
  rw [withDensity_apply _ hU.measurableSet, pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hfm,
    Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  intro h
  have h2 : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x ∉ U := by
    filter_upwards [h] with x hx hxU
    exact (hf.2.1 x).ne' (hx hxU)
  exact (hU.measure_pos volume hne).ne' (measure_eq_zero_iff_ae_notMem.2 h2)

theorem ae_exists_Ev (hf : IsRegularDensity f) (π : Fin m → ℝ) [Nonempty (Fin m)] :
    ∀ᵐ e ∂(μf f), ∃ i, e ∈ Ev π i := by
  have hac : μf f ≪ volume := withDensity_absolutelyContinuous _ _
  have hnull : (volume : Measure (Fin m → ℝ))
      (⋃ j, ⋃ k, {e : Fin m → ℝ | k ≠ j ∧ e k - e j = π j - π k}) = 0 := by
    refine measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
    by_cases hkj : k = j
    · simp [hkj]
    · exact measure_mono_null (fun e he => he.2) (tie_null j k hkj _)
  have h0 := hac hnull
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with e he
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun l => π l + e l) Finset.univ_nonempty
  refine ⟨j, fun k hkj => ?_⟩
  have hk2 := hj k (Finset.mem_univ _)
  rcases lt_or_eq_of_le hk2 with h | h
  · exact h
  · exact absurd (show e ∈ ⋃ j, ⋃ k, {e : Fin m → ℝ | k ≠ j ∧ e k - e j = π j - π k} from
      Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, hkj, by linarith⟩⟩) he

theorem sum_choiceProb (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    ∑ j, choiceProb f π j = 1 := by
  have := isProb hf
  have hdisj : Pairwise (Function.onFun Disjoint (Ev π)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro e ha hb
    exact Ev_disjoint π hab e ha hb
  have hU : μf f (⋃ i, Ev π i) = 1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion (measurableSet_Ev π))]
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_exists_Ev hf π] with e he hc
    exact hc (Set.mem_iUnion.2 he)
  rw [measure_iUnion hdisj (measurableSet_Ev π), tsum_fintype] at hU
  simp only [choiceProb_eq, Measure.real]
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), hU, ENNReal.toReal_one]

theorem choiceProb_pos (hf : IsRegularDensity f) (π : Fin m → ℝ) (i : Fin m) :
    0 < choiceProb f π i := by
  have := isProb hf
  rw [choiceProb_eq, Measure.real]
  exact ENNReal.toReal_pos (mu_pos hf (isOpen_Ev π i) (Ev_nonempty π i)).ne'
    (measure_ne_top _ _)

theorem choiceProb_nonneg (π : Fin m → ℝ) (i : Fin m) : 0 ≤ choiceProb f π i :=
  ENNReal.toReal_nonneg

theorem choiceProb_le_one (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ)
    (i : Fin m) : choiceProb f π i ≤ 1 := by
  rw [← sum_choiceProb hf π]
  exact Finset.single_le_sum (fun j _ => choiceProb_nonneg π j) (Finset.mem_univ i)

theorem mem_openSimplex (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    choiceProb f π ∈ openSimplex m :=
  ⟨fun i => choiceProb_pos hf π i, sum_choiceProb hf π⟩

theorem choiceProb_shift (π : Fin m → ℝ) (c : ℝ) :
    choiceProb f (fun j => π j + c) = choiceProb f π := by
  funext i
  have hE : Ev (fun j => π j + c) i = Ev π i := by
    ext e
    show (∀ j, j ≠ i → (π j + c) + e j < (π i + c) + e i) ↔ (∀ j, j ≠ i → π j + e j < π i + e i)
    constructor
    · intro h j hj; have := h j hj; linarith
    · intro h j hj; have := h j hj; linarith
  simp only [choiceProb_eq, hE]

theorem continuous_choiceProb (hf : IsRegularDensity f) : Continuous (choiceProb f) :=
  hf.2.2.2.2.continuous

/-! ### the potential -/

noncomputable def smax (x : Fin m → ℝ) : ℝ := ⨆ j, x j

theorem le_smax (x : Fin m → ℝ) (j : Fin m) : x j ≤ smax x :=
  le_ciSup (Finite.bddAbove_range x) j

theorem smax_le [Nonempty (Fin m)] {x : Fin m → ℝ} {c : ℝ} (h : ∀ j, x j ≤ c) : smax x ≤ c :=
  ciSup_le h

theorem exists_smax [Nonempty (Fin m)] (x : Fin m → ℝ) : ∃ j, smax x = x j := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := x)
  exact ⟨j, hj.symm⟩

theorem smax_add_const [Nonempty (Fin m)] (x : Fin m → ℝ) (c : ℝ) :
    smax (fun j => x j + c) = smax x + c := by
  apply le_antisymm
  · exact smax_le fun j => by linarith [le_smax x j]
  · obtain ⟨j, hj⟩ := exists_smax x
    rw [hj]; exact le_smax (fun j => x j + c) j

theorem smax_mono [Nonempty (Fin m)] {x y : Fin m → ℝ} (h : ∀ j, x j ≤ y j) : smax x ≤ smax y :=
  smax_le fun j => (h j).trans (le_smax y j)

theorem measurable_smax : Measurable (smax : (Fin m → ℝ) → ℝ) := by
  unfold smax
  exact Measurable.iSup fun j => measurable_pi_apply j

noncomputable def phi (π e : Fin m → ℝ) : ℝ := smax (fun j => π j + e j) - smax e

theorem abs_phi_le [Nonempty (Fin m)] (π e : Fin m → ℝ) : |phi π e| ≤ ‖π‖ := by
  have hb : ∀ j, |π j| ≤ ‖π‖ := fun j => by
    have := norm_le_pi_norm π j; rwa [Real.norm_eq_abs] at this
  rw [abs_le]
  constructor
  · have : smax e ≤ smax (fun j => π j + e j) + ‖π‖ := by
      apply smax_le; intro j
      have := le_smax (fun j => π j + e j) j
      have := (abs_le.1 (hb j)).1
      linarith
    unfold phi; linarith
  · have : smax (fun j => π j + e j) ≤ smax e + ‖π‖ := by
      apply smax_le; intro j
      have := le_smax e j
      have := (abs_le.1 (hb j)).2
      linarith
    unfold phi; linarith

theorem measurable_phi (π : Fin m → ℝ) : Measurable (phi π) := by
  unfold phi
  exact (measurable_smax.comp (by fun_prop)).sub measurable_smax

theorem integrable_phi (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    Integrable (phi π) (μf f) := by
  have := isProb hf
  exact Integrable.of_bound (measurable_phi π).aestronglyMeasurable ‖π‖
    (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact abs_phi_le π e)

/-- the potential `G(π) = E[max(π + ε) - max ε]` -/
noncomputable def G (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) : ℝ := ∫ e, phi π e ∂(μf f)

theorem smax_of_Ev [Nonempty (Fin m)] {π e : Fin m → ℝ} {i : Fin m} (h : e ∈ Ev π i) :
    smax (fun j => π j + e j) = π i + e i := by
  apply le_antisymm
  · apply smax_le; intro j
    by_cases hj : j = i
    · subst hj; exact le_rfl
    · exact (h j hj).le
  · exact le_smax (fun j => π j + e j) i

/-- `C π` is a subgradient of `G` at `π`. -/
theorem G_sub (hf : IsRegularDensity f) [Nonempty (Fin m)] (π π' : Fin m → ℝ) :
    choiceProb f π ⬝ᵥ (π' - π) ≤ G f π' - G f π := by
  have := isProb hf
  set g : (Fin m → ℝ) → ℝ := fun e => ∑ i, (Ev π i).indicator (fun _ => π' i - π i) e with hg
  have hgi : ∀ i, Integrable ((Ev π i).indicator (fun _ : Fin m → ℝ => π' i - π i)) (μf f) :=
    fun i => (integrable_const _).indicator (measurableSet_Ev π i)
  have hint : ∫ e, g e ∂(μf f) = choiceProb f π ⬝ᵥ (π' - π) := by
    rw [hg, integral_finsetSum _ (fun i _ => hgi i)]
    simp only [dotProduct, choiceProb_eq, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (measurableSet_Ev π i), smul_eq_mul]
  rw [← hint, G, G, ← integral_sub (integrable_phi hf π') (integrable_phi hf π)]
  refine integral_mono_ae (integrable_finsetSum _ (fun i _ => hgi i))
    ((integrable_phi hf π').sub (integrable_phi hf π)) ?_
  filter_upwards [ae_exists_Ev hf π] with e he
  obtain ⟨i, hi⟩ := he
  have hgv : g e = π' i - π i := by
    rw [hg]
    simp only
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hi]
    · intro j _ hji
      rw [Set.indicator_of_notMem]
      intro hj
      exact Ev_disjoint π hji e hj hi
    · simp
  rw [hgv]
  simp only [Pi.sub_apply, phi]
  rw [smax_of_Ev hi]
  have := le_smax (fun j => π' j + e j) i
  linarith

theorem abs_dot_le (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ) :
    |choiceProb f π ⬝ᵥ z| ≤ ∑ i, |z i| := by
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (choiceProb_nonneg π i)]
  exact mul_le_of_le_one_left (abs_nonneg _) (choiceProb_le_one hf π i)

theorem continuous_G (hf : IsRegularDensity f) [Nonempty (Fin m)] : Continuous (G f) := by
  have key : ∀ a b : Fin m → ℝ, dist (G f a) (G f b) ≤ (Fintype.card (Fin m) : ℝ) * dist a b := by
    intro a b
    have h1 := G_sub hf a b
    have h2 := G_sub hf b a
    have h3 := abs_dot_le hf a (b - a)
    have h4 := abs_dot_le hf b (a - b)
    have h5 : ∑ i, |(b - a) i| ≤ (Fintype.card (Fin m) : ℝ) * dist a b := by
      have : ∀ i ∈ Finset.univ, |(b - a) i| ≤ dist a b := fun i _ => by
        rw [Pi.sub_apply, abs_sub_comm, ← Real.dist_eq]; exact dist_le_pi_dist a b i
      have := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_univ] using this
    have h6 : ∑ i, |(a - b) i| = ∑ i, |(b - a) i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [abs_sub_comm]
    rw [Real.dist_eq, abs_le]
    constructor
    · have := (abs_le.1 h4).1; linarith
    · have := (abs_le.1 h3).1; linarith
  have hK : 0 ≤ (Fintype.card (Fin m) : ℝ) := by positivity
  exact (LipschitzWith.of_dist_le_mul (K := ⟨_, hK⟩) key).continuous

theorem G_shift (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) (c : ℝ) :
    G f (fun j => π j + c) = G f π + c := by
  have := isProb hf
  have : ∀ e, phi (fun j => π j + c) e = phi π e + c := by
    intro e
    simp only [phi]
    have := smax_add_const (fun j => π j + e j) c
    have h2 : (fun j => π j + c + e j) = (fun j => (π j + e j) + c) := by funext j; ring
    rw [h2, this]; ring
  simp only [G, this]
  rw [integral_add (integrable_phi hf π) (integrable_const c), integral_const]
  simp

theorem G_zero (hf : IsRegularDensity f) [Nonempty (Fin m)] : G f 0 = 0 := by
  have : ∀ e : Fin m → ℝ, phi 0 e = 0 := by
    intro e; simp [phi]
  simp [G, this]

/-- Lower bound used for coercivity. -/
theorem G_lower (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) (k : Fin m)
    (lo R : ℝ) (hlo : ∀ j, lo ≤ π j) (hR : 0 ≤ R) :
    lo + (μf f).real (Metric.closedBall (0 : Fin m → ℝ) R) * (π k - lo) - 2 * R ≤ G f π := by
  have := isProb hf
  set B := Metric.closedBall (0 : Fin m → ℝ) R
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hint : Integrable (fun e => B.indicator (fun _ => π k - lo) e + (lo - 2 * R)) (μf f) :=
    ((integrable_const _).indicator hB).add (integrable_const _)
  have hval : ∫ e, (B.indicator (fun _ => π k - lo) e + (lo - 2 * R)) ∂(μf f) =
      lo + (μf f).real B * (π k - lo) - 2 * R := by
    rw [integral_add ((integrable_const _).indicator hB) (integrable_const _),
      integral_indicator_const _ hB, integral_const]
    simp; ring
  rw [← hval, G]
  refine integral_mono hint (integrable_phi hf π) fun e => ?_
  have hlow : lo ≤ phi π e := by
    simp only [phi]
    have := smax_mono (x := fun j => e j + lo) (y := fun j => π j + e j) (fun j => by
      show e j + lo ≤ π j + e j; linarith [hlo j])
    rw [smax_add_const] at this
    linarith
  by_cases he : e ∈ B
  · rw [Set.indicator_of_mem he]
    have hb : ∀ j, |e j| ≤ R := by
      intro j
      have h1 : ‖e‖ ≤ R := by simpa [B] using he
      have := norm_le_pi_norm e j
      rw [Real.norm_eq_abs] at this; linarith
    have h1 : smax e ≤ R := smax_le fun j => (abs_le.1 (hb j)).2
    have h2 := le_smax (fun j => π j + e j) k
    have h3 := (abs_le.1 (hb k)).1
    simp only [phi] at *
    linarith
  · rw [Set.indicator_of_notMem he]
    linarith


/-! ### critical points, surjectivity, argmax -/

theorem crit (hf : IsRegularDensity f) [Nonempty (Fin m)] (y π0 : Fin m → ℝ)
    (h : ∀ s : ℝ, 0 < s → G f π0 - y ⬝ᵥ π0 ≤
        G f (π0 - s • (choiceProb f π0 - y)) - y ⬝ᵥ (π0 - s • (choiceProb f π0 - y))) :
    choiceProb f π0 = y := by
  set z := choiceProb f π0 - y with hz
  have key : ∀ s : ℝ, 0 < s → (choiceProb f (π0 - s • z) - y) ⬝ᵥ z ≤ 0 := by
    intro s hs
    have h1 := h s hs
    have h2 := G_sub hf (π0 - s • z) π0
    have e1 : π0 - (π0 - s • z) = s • z := by abel
    rw [e1, dotProduct_smul, smul_eq_mul] at h2
    have e2 : y ⬝ᵥ (π0 - s • z) = y ⬝ᵥ π0 - s * (y ⬝ᵥ z) := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [e2] at h1
    rw [sub_dotProduct]
    have h3 : s * (choiceProb f (π0 - s • z) ⬝ᵥ z) ≤ s * (y ⬝ᵥ z) := by linarith
    have := le_of_mul_le_mul_left h3 hs
    linarith
  have hC := continuous_choiceProb hf
  have hcont : Continuous fun s : ℝ => (choiceProb f (π0 - s • z) - y) ⬝ᵥ z := by
    simp only [dotProduct]
    fun_prop
  have hlim : (choiceProb f (π0 - (0 : ℝ) • z) - y) ⬝ᵥ z ≤ 0 :=
    le_of_tendsto ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun s hs => key s hs)
  rw [zero_smul, sub_zero, ← hz] at hlim
  have hnn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hz0 : z = 0 := dotProduct_self_eq_zero.1 (le_antisymm hlim hnn)
  rw [hz] at hz0
  exact sub_eq_zero.1 hz0

theorem fenchel (hf : IsRegularDensity f) [Nonempty (Fin m)] (p π : Fin m → ℝ) :
    choiceProb f p ⬝ᵥ π - G f π ≤ choiceProb f p ⬝ᵥ p - G f p := by
  have := G_sub hf p π
  rw [dotProduct_sub] at this
  linarith

theorem surj (hf : IsRegularDensity f) [Nonempty (Fin m)] (y : Fin m → ℝ)
    (hy : y ∈ openSimplex m) : ∃ π, choiceProb f π = y ∧ ∑ i, π i = 0 := by
  have := isProb hf
  obtain ⟨hpos, hsum⟩ := hy
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos_iff_nonempty.2 ‹_›
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ y Finset.univ_nonempty
  set δ := y i0 with hδdef
  have hδ : 0 < δ := hpos i0
  have hyδ : ∀ i, δ ≤ y i := fun i => hi0 i (Finset.mem_univ _)
  have hlim : Tendsto (fun n : ℕ => (μf f).real (Metric.closedBall (0 : Fin m → ℝ) n)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => μf f (Metric.closedBall (0 : Fin m → ℝ) n)) atTop
        (𝓝 (μf f (⋃ n : ℕ, Metric.closedBall (0 : Fin m → ℝ) n))) :=
      tendsto_measure_iUnion_atTop (fun a b hab =>
        Metric.closedBall_subset_closedBall (by exact_mod_cast hab))
    rw [Metric.iUnion_closedBall_nat, measure_univ] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    exact h2
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (show 1 - δ / 2 < 1 by linarith))).exists
  set R : ℝ := ((n : ℕ) : ℝ) with hRdef
  have hR : 0 ≤ R := Nat.cast_nonneg n
  set p := (μf f).real (Metric.closedBall (0 : Fin m → ℝ) R) with hpdef
  have hp : 1 - δ / 2 < p := hn
  set H : (Fin m → ℝ) → ℝ := fun π => G f π - y ⬝ᵥ π with hHdef
  have hcoer : ∀ π : Fin m → ℝ, ∑ i, π i = 0 → δ / 2 * ‖π‖ - 2 * R ≤ H π := by
    intro π hπ
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ π Finset.univ_nonempty
    obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ π Finset.univ_nonempty
    set lo := π k0 with hlodef
    have hlo : ∀ j, lo ≤ π j := fun j => hk0 j (Finset.mem_univ _)
    have hhi : ∀ j, π j ≤ π k := fun j => hk j (Finset.mem_univ _)
    have hd : 0 ≤ π k - lo := by linarith [hlo k]
    have hG := G_lower hf π k lo R hlo hR
    have e1 : y ⬝ᵥ π = lo + ∑ i, y i * (π i - lo) := by
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
      ring
    have e2 : ∑ i, y i * (π i - lo) = ∑ i ∈ Finset.univ.erase k0, y i * (π i - lo) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0)]
      simp [hlodef]
    have e3 : ∑ i ∈ Finset.univ.erase k0, y i * (π i - lo) ≤
        ∑ i ∈ Finset.univ.erase k0, y i * (π k - lo) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hhi i]) (hpos i).le
    have e4 : ∑ i ∈ Finset.univ.erase k0, y i * (π k - lo) = (1 - y k0) * (π k - lo) := by
      rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ _), hsum]
    have e5 : (1 - y k0) * (π k - lo) ≤ (1 - δ) * (π k - lo) :=
      mul_le_mul_of_nonneg_right (by linarith [hyδ k0]) hd
    have hp1 : p ≤ 1 := by
      rw [hpdef]; exact measureReal_le_one
    have hlo0 : lo ≤ 0 := by
      by_contra hc
      push_neg at hc
      have : 0 < ∑ i, π i :=
        Finset.sum_pos (fun i _ => lt_of_lt_of_le hc (hlo i)) Finset.univ_nonempty
      linarith
    have hhi0 : 0 ≤ π k := by
      by_contra hc
      push_neg at hc
      have : ∑ i, π i < 0 :=
        Finset.sum_neg (fun i _ => lt_of_le_of_lt (hhi i) hc) Finset.univ_nonempty
      linarith
    have hnorm : ‖π‖ ≤ π k - lo := by
      refine (pi_norm_le_iff_of_nonneg hd).2 fun i => ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [hlo i]
      · linarith [hhi i]
    have hmul : δ / 2 * (π k - lo) ≤ (p - 1 + δ) * (π k - lo) :=
      mul_le_mul_of_nonneg_right (by linarith) hd
    have hmul2 : δ / 2 * ‖π‖ ≤ δ / 2 * (π k - lo) :=
      mul_le_mul_of_nonneg_left hnorm (by linarith)
    show δ / 2 * ‖π‖ - 2 * R ≤ G f π - y ⬝ᵥ π
    nlinarith
  set r : ℝ := (2 * R + 1) * 2 / δ with hrdef
  have hr0 : 0 ≤ r := by positivity
  set K := {π : Fin m → ℝ | ∑ i, π i = 0} ∩ Metric.closedBall 0 r with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Fin m → ℝ) r).inter_left
    (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
  have h0K : (0 : Fin m → ℝ) ∈ K := ⟨by simp, by simpa using hr0⟩
  have hGc := continuous_G hf
  have hHc : Continuous H := by
    simp only [hHdef, dotProduct]
    fun_prop
  obtain ⟨π1, hπ1K, hmin⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hHc.continuousOn
  have hglob : ∀ π, H π1 ≤ H π := by
    intro π
    set c := (∑ i, π i) / m with hc
    set π0 : Fin m → ℝ := fun j => π j + (-c) with hπ0
    have hs0 : ∑ i, π0 i = 0 := by
      simp only [hπ0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hc]
      field_simp
      ring
    have hH0 : H π0 = H π := by
      simp only [hHdef, hπ0]
      rw [G_shift hf]
      simp only [dotProduct, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
      ring
    rw [← hH0]
    by_cases hr : ‖π0‖ ≤ r
    · exact hmin ⟨hs0, by simpa using hr⟩
    · have h1 := hcoer π0 hs0
      have h2 : H π1 ≤ H 0 := hmin h0K
      have h3 : H 0 = 0 := by simp [hHdef, G_zero hf]
      have h4 : δ / 2 * r = 2 * R + 1 := by
        rw [hrdef]; field_simp
      push_neg at hr
      have h5 : δ / 2 * r < δ / 2 * ‖π0‖ := mul_lt_mul_of_pos_left hr (by linarith)
      linarith
  refine ⟨π1, crit hf y π1 fun s _ => hglob _, hπ1K.1⟩

theorem argmax_of (hf : IsRegularDensity f) [Nonempty (Fin m)] (V : (Fin m → ℝ) → ℝ)
    (hV : ∀ y ∈ openSimplex m, ∃ p, choiceProb f p = y ∧ V y = y ⬝ᵥ p - G f p) :
    IsPerturbedArgmax V (choiceProb f) := by
  intro π
  refine ⟨mem_openSimplex hf π, fun y hy hne => ?_⟩
  obtain ⟨p, hp, hVy⟩ := hV y hy
  obtain ⟨q, hq, hVq⟩ := hV (choiceProb f π) (mem_openSimplex hf π)
  have hVC : V (choiceProb f π) = choiceProb f π ⬝ᵥ π - G f π := by
    rw [hVq]
    have a1 := fenchel hf q π
    have a2 := fenchel hf π q
    rw [hq] at a1
    linarith
  rw [hVC, hVy]
  have hle := fenchel hf p π
  rw [hp] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · linarith
  · exfalso
    apply hne
    symm
    apply crit hf y π
    intro s _
    have := fenchel hf p (π - s • (choiceProb f π - y))
    rw [hp] at this
    linarith


/-! ### strict monotonicity of `C` -/

theorem dot_eq_integral (hf : IsRegularDensity f) (π z : Fin m → ℝ) :
    choiceProb f π ⬝ᵥ z = ∫ e, ∑ i, (Ev π i).indicator (fun _ => z i) e ∂(μf f) := by
  have := isProb hf
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (measurableSet_Ev π i))]
  simp only [dotProduct, choiceProb_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator_const _ (measurableSet_Ev π i), smul_eq_mul]

theorem gsum_of_mem {π e : Fin m → ℝ} (z : Fin m → ℝ) {i : Fin m} (hi : e ∈ Ev π i) :
    ∑ j, (Ev π j).indicator (fun _ => z j) e = z i := by
  rw [Finset.sum_eq_single i]
  · simp [Set.indicator_of_mem hi]
  · intro j _ hji
    rw [Set.indicator_of_notMem]
    intro hj
    exact Ev_disjoint π hji e hj hi
  · simp

theorem diff_lower (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ) {a b : Fin m}
    {t : ℝ} (ht : 0 < t) :
    (z a - z b) * (μf f).real (Ev π b ∩ Ev (π + t • z) a) ≤
      (choiceProb f (π + t • z) - choiceProb f π) ⬝ᵥ z := by
  have := isProb hf
  set π' := π + t • z with hπ'
  set E := Ev π b ∩ Ev π' a with hEdef
  have hE : MeasurableSet E := (measurableSet_Ev π b).inter (measurableSet_Ev π' a)
  have hint : ∀ p : Fin m → ℝ,
      Integrable (fun e => ∑ i, (Ev p i).indicator (fun _ => z i) e) (μf f) :=
    fun p => integrable_finsetSum _
      (fun i _ => (integrable_const _).indicator (measurableSet_Ev p i))
  rw [sub_dotProduct, dot_eq_integral hf, dot_eq_integral hf, ← integral_sub (hint _) (hint _)]
  rw [show (z a - z b) * (μf f).real E = ∫ e, E.indicator (fun _ => z a - z b) e ∂(μf f) by
    rw [integral_indicator_const _ hE, smul_eq_mul, mul_comm]]
  refine integral_mono_ae ((integrable_const _).indicator hE) ((hint _).sub (hint _)) ?_
  filter_upwards [ae_exists_Ev hf π, ae_exists_Ev hf π'] with e he he'
  obtain ⟨i, hi⟩ := he
  obtain ⟨j, hj⟩ := he'
  show E.indicator (fun _ => z a - z b) e ≤
    ∑ i, (Ev π' i).indicator (fun _ => z i) e - ∑ i, (Ev π i).indicator (fun _ => z i) e
  rw [gsum_of_mem z hi, gsum_of_mem z hj]
  by_cases heE : e ∈ E
  · rw [Set.indicator_of_mem heE]
    have hib : i = b := by
      by_contra h; exact Ev_disjoint π h e hi heE.1
    have hja : j = a := by
      by_contra h; exact Ev_disjoint π' h e hj heE.2
    rw [hib, hja]
  · rw [Set.indicator_of_notMem heE]
    by_cases hij : i = j
    · rw [hij, sub_self]
    · have h1 := hi j (Ne.symm hij)
      have h2 := hj i hij
      simp only [hπ', Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : t * z i < t * z j := by linarith
      have := lt_of_mul_lt_mul_left h3 ht.le
      linarith

/-- the shear `e ↦ e - (e a) • 𝟙_b` -/
noncomputable def shear {m : ℕ} (a b : Fin m) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.transvection (-(LinearMap.proj a : (Fin m → ℝ) →ₗ[ℝ] ℝ)) (Pi.single b 1)

theorem shear_apply {m : ℕ} (a b : Fin m) (e : Fin m → ℝ) (k : Fin m) :
    shear a b e k = e k - (if k = b then e a else 0) := by
  simp only [shear, LinearMap.transvection.apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.neg_apply, LinearMap.coe_proj, Function.eval, Pi.single_apply]
  split_ifs <;> ring

theorem det_shear {m : ℕ} {a b : Fin m} (hab : a ≠ b) : LinearMap.det (shear a b) = 1 := by
  rw [shear, LinearMap.transvection.det]
  simp [Pi.single_apply, hab]

theorem box_lower (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ) {a b : Fin m}
    (hab : a ≠ b) (hD : 0 < z a - z b) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      c * t ≤ (μf f).real (Ev π b ∩ Ev (π + t • z) a) := by
  have := isProb hf
  set D := z a - z b with hDdef
  set N : ℝ := 2 + 2 * ‖z‖ with hN
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hπ0 : 0 ≤ ‖π‖ := norm_nonneg π
  set ρ : ℝ := ‖π‖ + N + 2 + D with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ, hN]; positivity
  obtain ⟨e0, -, hmin⟩ := (isCompact_closedBall (0 : Fin m → ℝ) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ0⟩ hf.1.continuousOn
  have hf0 : 0 < (f e0).toReal := ENNReal.toReal_pos (hf.2.1 e0).ne' (hf.2.2.1 e0)
  refine ⟨(f e0).toReal * D, mul_pos hf0 hD, fun t ht ht1 => ?_⟩
  have hπb : ∀ j, |π j| ≤ ‖π‖ := fun j => by
    have := norm_le_pi_norm π j; rwa [Real.norm_eq_abs] at this
  have hzt : ∀ j, |t * z j| ≤ ‖z‖ := fun j => by
    have := norm_le_pi_norm z j
    rw [Real.norm_eq_abs] at this
    rw [abs_mul, abs_of_pos ht]
    nlinarith [abs_nonneg (z j)]
  set lo : Fin m → ℝ := fun k => if k = a then -π a else if k = b then π a - π b else -N - 1 - π k
    with hlo
  set hi : Fin m → ℝ := fun k => lo k + (if k = b then t * D else 1) with hhi
  set Box : Set (Fin m → ℝ) := Set.pi Set.univ fun k => Set.Ioo (lo k) (hi k) with hBox
  set S := (shear a b) ⁻¹' Box with hS
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun k => measurableSet_Ioo
  have hSm : MeasurableSet S :=
    hBm.preimage (LinearMap.continuous_of_finiteDimensional (shear a b)).measurable
  -- coordinates of points of S
  have hcoord : ∀ e ∈ S, (-π a < e a ∧ e a < 1 - π a) ∧
      (π a - π b < e b - e a ∧ e b - e a < π a - π b + t * D) ∧
      (∀ k, k ≠ a → k ≠ b → -N - 1 - π k < e k ∧ e k < -N - π k) := by
    intro e he
    have hk : ∀ k, lo k < shear a b e k ∧ shear a b e k < hi k := fun k =>
      (Set.mem_univ_pi.1 he) k
    refine ⟨?_, ?_, ?_⟩
    · have := hk a
      simp only [shear_apply, hlo, hhi, if_neg hab, if_neg (Ne.symm hab), ↓reduceIte, sub_zero] at this
      constructor <;> linarith [this.1, this.2]
    · have := hk b
      simp only [shear_apply, hlo, hhi, if_neg hab, if_neg (Ne.symm hab), ↓reduceIte, sub_zero] at this
      constructor <;> linarith [this.1, this.2]
    · intro k hka hkb
      have := hk k
      simp only [shear_apply, hlo, hhi, if_neg hka, if_neg hkb, ↓reduceIte, sub_zero] at this
      constructor <;> linarith [this.1, this.2]
  have hSE : S ⊆ Ev π b ∩ Ev (π + t • z) a := by
    intro e he
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hk⟩ := hcoord e he
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · by_cases hja : j = a
      · rw [hja]; linarith
      · have := hk j hja hj; linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hjb : j = b
      · rw [hjb]; rw [hDdef] at hb2; linarith
      · have := hk j hj hjb
        have h1 := (abs_le.1 (hzt j)).2
        have h2 := (abs_le.1 (hzt a)).1
        linarith
  have hSball : S ⊆ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    intro e he
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hk⟩ := hcoord e he
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hρ0).2 fun j => ?_
    rw [Real.norm_eq_abs, abs_le]
    have hpj := abs_le.1 (hπb j)
    have hpa := abs_le.1 (hπb a)
    have hpb := abs_le.1 (hπb b)
    have htD : t * D ≤ D := by nlinarith
    have htD0 : 0 ≤ t * D := by positivity
    by_cases hja : j = a
    · rw [hja]; constructor <;> linarith
    · by_cases hjb : j = b
      · rw [hjb]; constructor <;> linarith
      · have := hk j hja hjb; constructor <;> linarith
  have hvolS : volume S = ENNReal.ofReal (t * D) := by
    rw [hS, Measure.addHaar_preimage_linearMap _ (by rw [det_shear hab]; norm_num), det_shear hab]
    simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul, hBox]
    rw [Real.volume_pi_Ioo]
    have : ∀ k, hi k - lo k = if k = b then t * D else 1 := fun k => by
      simp only [hhi]; ring
    simp only [this]
    rw [Finset.prod_eq_single b]
    · simp
    · intro k _ hkb; simp [hkb]
    · simp
  have hμS : f e0 * ENNReal.ofReal (t * D) ≤ μf f S := by
    rw [withDensity_apply _ hSm, ← hvolS, ← setLIntegral_const]
    exact setLIntegral_mono' hSm fun e he => hmin (hSball he)
  have hle : (μf f).real S ≤ (μf f).real (Ev π b ∩ Ev (π + t • z) a) := measureReal_mono hSE
  have h2 : (f e0 * ENNReal.ofReal (t * D)).toReal ≤ (μf f).real S :=
    ENNReal.toReal_mono (measure_ne_top _ _) hμS
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  calc (f e0).toReal * D * t = (f e0).toReal * (t * D) := by ring
    _ ≤ _ := h2.trans hle

theorem dC_pos (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ)
    (hz : ∑ i, z i = 0) (hz0 : z ≠ 0) : 0 < (fderiv ℝ (choiceProb f) π z) ⬝ᵥ z := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ z Finset.univ_nonempty
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ z Finset.univ_nonempty
  have hab : ∀ i, z b ≤ z i ∧ z i ≤ z a :=
    fun i => ⟨hb i (Finset.mem_univ _), ha i (Finset.mem_univ _)⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos_iff_nonempty.2 ‹_›
  have hD : 0 < z a - z b := by
    by_contra hc
    push_neg at hc
    apply hz0
    have hall : ∀ i, z i = z a := fun i => le_antisymm (hab i).2 (by linarith [(hab i).1])
    have hs : ∑ i, z i = m * z a := by
      rw [Finset.sum_congr rfl fun i _ => hall i]; simp
    have hza : z a = 0 := by
      rw [hz] at hs
      exact (mul_eq_zero.1 hs.symm).resolve_left hm0.ne'
    funext i; rw [hall i, hza]; rfl
  have hne : a ≠ b := by
    intro h; rw [h, sub_self] at hD; exact lt_irrefl _ hD
  obtain ⟨c, hc, hcb⟩ := box_lower hf π z hne hD
  have hdiff : DifferentiableAt ℝ (choiceProb f) π := (hf.2.2.2.2.differentiable one_ne_zero) π
  have hπ : π + (0 : ℝ) • z = π := by simp
  have hline : HasDerivAt (fun s : ℝ => π + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add π
  have hC' : HasDerivAt (fun s : ℝ => choiceProb f (π + s • z))
      (fderiv ℝ (choiceProb f) (π + (0 : ℝ) • z) z) 0 := by
    have hdiff0 : DifferentiableAt ℝ (choiceProb f) (π + (0 : ℝ) • z) :=
      (hf.2.2.2.2.differentiable one_ne_zero) _
    exact hdiff0.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  rw [hπ] at hC'
  set g : ℝ → ℝ := fun s => choiceProb f (π + s • z) ⬝ᵥ z with hgdef
  have hg : HasDerivAt g ((fderiv ℝ (choiceProb f) π z) ⬝ᵥ z) 0 := by
    simp only [hgdef, dotProduct]
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.1 hC' i).mul_const (z i)
  have hsl := hg.tendsto_slope_zero_right
  have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (z a - z b) * c ≤ t⁻¹ • (g (0 + t) - g 0) := by
    intro t ht
    have h1 := diff_lower hf π z (a := a) (b := b) ht.1
    have h2 := hcb t ht.1 ht.2.le
    have e : g (0 + t) - g 0 = (choiceProb f (π + t • z) - choiceProb f π) ⬝ᵥ z := by
      simp [hgdef, sub_dotProduct]
    rw [e, smul_eq_mul, le_inv_mul_iff₀ ht.1]
    calc t * ((z a - z b) * c) = (z a - z b) * (c * t) := by ring
      _ ≤ (z a - z b) * (μf f).real (Ev π b ∩ Ev (π + t • z) a) :=
          mul_le_mul_of_nonneg_left h2 hD.le
      _ ≤ _ := h1
  have hge : (z a - z b) * c ≤ (fderiv ℝ (choiceProb f) π z) ⬝ᵥ z :=
    ge_of_tendsto hsl (by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hbound t ht)
  exact lt_of_lt_of_le (mul_pos hD hc) hge

/-! ### the map `Φ`, its inverse, and the perturbation `V` -/

noncomputable def Lsum (m : ℕ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z _ => (∑ j, z j) / m
      map_add' := fun x y => by
        funext i; simp [Finset.sum_add_distrib, add_div]
      map_smul' := fun c x => by
        funext i; simp; rw [← Finset.mul_sum, mul_div_assoc] }

theorem Lsum_apply (z : Fin m → ℝ) (i : Fin m) : Lsum m z i = (∑ j, z j) / m := rfl

theorem sum_Lsum [Nonempty (Fin m)] (z : Fin m → ℝ) : ∑ i, Lsum m z i = ∑ j, z j := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have := Fin.pos_iff_nonempty.2 ‹_›; positivity
  simp only [Lsum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

noncomputable def Phi (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) : Fin m → ℝ :=
  choiceProb f π + Lsum m π

theorem sum_Phi (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    ∑ i, Phi f π i = 1 + ∑ j, π j := by
  simp only [Phi, Pi.add_apply, Finset.sum_add_distrib, sum_choiceProb hf, sum_Lsum]

theorem line_deriv (hf : IsRegularDensity f) (π z : Fin m → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => choiceProb f (π + r • z))
      (fderiv ℝ (choiceProb f) (π + s • z) z) s := by
  have hdiff : DifferentiableAt ℝ (choiceProb f) (π + s • z) :=
    (hf.2.2.2.2.differentiable one_ne_zero) _
  have hline : HasDerivAt (fun r : ℝ => π + r • z) z s := by
    simpa using ((hasDerivAt_id s).smul_const z).const_add π
  exact hdiff.hasFDerivAt.comp_hasDerivAt s hline

theorem dC_sum (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ) :
    ∑ i, fderiv ℝ (choiceProb f) π z i = 0 := by
  have h1 := line_deriv hf π z 0
  have h2 : HasDerivAt (fun r : ℝ => ∑ i, choiceProb f (π + r • z) i)
      (∑ i, fderiv ℝ (choiceProb f) (π + (0 : ℝ) • z) z i) 0 :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_pi.1 h1 i
  have h3 : (fun r : ℝ => ∑ i, choiceProb f (π + r • z) i) = fun _ => 1 := by
    funext r; exact sum_choiceProb hf _
  rw [h3, zero_smul, add_zero] at h2
  exact h2.unique (hasDerivAt_const 0 _)

noncomputable def DPhi (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  fderiv ℝ (choiceProb f) π + Lsum m

theorem hasFDerivAt_Phi (hf : IsRegularDensity f) (π : Fin m → ℝ) :
    HasFDerivAt (Phi f) (DPhi f π) π :=
  ((hf.2.2.2.2.differentiable one_ne_zero) π).hasFDerivAt.add (Lsum m).hasFDerivAt

theorem contDiff_Phi (hf : IsRegularDensity f) : ContDiff ℝ 1 (Phi f) :=
  hf.2.2.2.2.add (Lsum m).contDiff

theorem DPhi_sum (hf : IsRegularDensity f) [Nonempty (Fin m)] (π u : Fin m → ℝ) :
    ∑ i, DPhi f π u i = ∑ j, u j := by
  simp only [DPhi, ContinuousLinearMap.add_apply, Pi.add_apply, Finset.sum_add_distrib,
    dC_sum hf, sum_Lsum, zero_add]

theorem DPhi_inj (hf : IsRegularDensity f) [Nonempty (Fin m)] (π u : Fin m → ℝ)
    (hu : DPhi f π u = 0) : u = 0 := by
  have hs0 : ∑ j, u j = 0 := by rw [← DPhi_sum hf π u, hu]; simp
  have hL : Lsum m u = 0 := by funext i; simp [Lsum_apply, hs0]
  have hD : fderiv ℝ (choiceProb f) π u = 0 := by
    have := hu
    simp only [DPhi, ContinuousLinearMap.add_apply, hL, add_zero] at this
    exact this
  by_contra hne
  have := dC_pos hf π u hs0 hne
  rw [hD] at this
  simp at this

noncomputable def DPhiE (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (LinearEquiv.ofInjectiveEndo (DPhi f π : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (fun u v huv => by
    have h : DPhi f π (u - v) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 huv
    exact sub_eq_zero.1 (DPhi_inj hf π _ h))).toContinuousLinearEquiv

theorem DPhiE_coe (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    (DPhiE hf π : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) = DPhi f π := by
  ext u i; rfl

theorem Phi_inj (hf : IsRegularDensity f) [Nonempty (Fin m)] : Function.Injective (Phi f) := by
  intro p q hpq
  have hs : ∑ j, p j = ∑ j, q j := by
    have := congrArg (fun v : Fin m → ℝ => ∑ i, v i) hpq
    beta_reduce at this
    rw [sum_Phi hf, sum_Phi hf] at this
    linarith
  have hL : Lsum m p = Lsum m q := by funext i; simp [Lsum_apply, hs]
  have hC : choiceProb f p = choiceProb f q := by
    have := hpq
    simp only [Phi, hL] at this
    exact add_right_cancel this
  by_contra hne
  set z := q - p with hzdef
  have hz : ∑ i, z i = 0 := by simp [hzdef, Finset.sum_sub_distrib, hs]
  have hz0 : z ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set h : ℝ → ℝ := fun r => choiceProb f (p + r • z) ⬝ᵥ z with hhdef
  have hd : ∀ s, HasDerivAt h ((fderiv ℝ (choiceProb f) (p + s • z) z) ⬝ᵥ z) s := by
    intro s
    simp only [hhdef, dotProduct]
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.1 (line_deriv hf p z s) i).mul_const (z i)
  have hmono : StrictMono h := strictMono_of_deriv_pos fun s => by
    rw [(hd s).deriv]; exact dC_pos hf _ z hz hz0
  have h01 := hmono (zero_lt_one' ℝ)
  have e0 : h 0 = choiceProb f p ⬝ᵥ z := by simp [hhdef]
  have e1 : h 1 = choiceProb f q ⬝ᵥ z := by simp [hhdef, hzdef]
  rw [e0, e1, hC] at h01
  exact lt_irrefl _ h01

noncomputable def psi (f : (Fin m → ℝ) → ℝ≥0∞) : (Fin m → ℝ) → (Fin m → ℝ) :=
  Function.invFun (Phi f)

theorem Phi_psi (hf : IsRegularDensity f) [Nonempty (Fin m)] {y : Fin m → ℝ}
    (hy : y ∈ openSimplex m) : Phi f (psi f y) = y := by
  obtain ⟨π, hπ, hs⟩ := surj hf y hy
  have : Phi f π = y := by
    funext i; simp [Phi, Lsum_apply, hs, hπ]
  exact Function.invFun_eq ⟨π, this⟩

theorem psi_spec (hf : IsRegularDensity f) [Nonempty (Fin m)] {y : Fin m → ℝ}
    (hy : y ∈ openSimplex m) : choiceProb f (psi f y) = y ∧ ∑ j, psi f y j = 0 := by
  have h := Phi_psi hf hy
  have hs : ∑ j, psi f y j = 0 := by
    have := congrArg (fun v : Fin m → ℝ => ∑ i, v i) h
    beta_reduce at this
    rw [sum_Phi hf, hy.2] at this
    linarith
  refine ⟨?_, hs⟩
  have hL : Lsum m (psi f y) = 0 := by funext i; simp [Lsum_apply, hs]
  have h2 := h
  simp only [Phi, hL, add_zero] at h2
  exact h2

theorem psi_smooth (hf : IsRegularDensity f) [Nonempty (Fin m)] {y : Fin m → ℝ}
    (hy : y ∈ openSimplex m) :
    ContDiffAt ℝ 1 (psi f) y ∧
      HasFDerivAt (psi f) ((DPhiE hf (psi f y)).symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) y := by
  have hy' : Phi f (psi f y) = y := Phi_psi hf hy
  set π0 := psi f y with hπ0
  have hPhi : ContDiffAt ℝ 1 (Phi f) π0 := (contDiff_Phi hf).contDiffAt
  have hder : HasFDerivAt (Phi f) ((DPhiE hf π0 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))) π0 := by
    rw [DPhiE_coe]; exact hasFDerivAt_Phi hf π0
  have hs := hPhi.hasStrictFDerivAt' hder one_ne_zero
  have hev : ∀ᶠ x in 𝓝 (Phi f π0), psi f x = hs.localInverse (Phi f) _ π0 x :=
    hs.localInverse_unique (Eventually.of_forall fun x =>
      Function.leftInverse_invFun (Phi_inj hf) x)
  have h1 : ContDiffAt ℝ 1 (psi f) (Phi f π0) :=
    (hPhi.to_localInverse hder one_ne_zero).congr_of_eventuallyEq hev
  have h2 : HasFDerivAt (psi f) ((DPhiE hf π0).symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))
      (Phi f π0) :=
    hs.to_localInverse.hasFDerivAt.congr_of_eventuallyEq hev
  rw [hy'] at h1 h2
  exact ⟨h1, h2⟩

/-- the perturbation -/
noncomputable def Vf (f : (Fin m → ℝ) → ℝ≥0∞) (y : Fin m → ℝ) : ℝ :=
  y ⬝ᵥ psi f y - G f (psi f y)

def Uset (m : ℕ) : Set (Fin m → ℝ) := {w | ∀ i, 0 < planeProj m w i}

noncomputable def Pl (m : ℕ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.id ℝ _ - Lsum m

theorem planeProj_eq : planeProj m = fun w => Pl m w + fun _ => 1 / (m : ℝ) := by
  funext w i
  simp only [planeProj, Pl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    Pi.add_apply, Pi.sub_apply, Lsum_apply]
  ring

theorem hasFDerivAt_planeProj (w : Fin m → ℝ) : HasFDerivAt (planeProj m) (Pl m) w := by
  rw [planeProj_eq]; exact (Pl m).hasFDerivAt.add_const _

theorem contDiff_planeProj : ContDiff ℝ 1 (planeProj m) := by
  rw [planeProj_eq]; exact (Pl m).contDiff.add contDiff_const

theorem planeProj_mem [Nonempty (Fin m)] {w : Fin m → ℝ} (hw : w ∈ Uset m) :
    planeProj m w ∈ openSimplex m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have := Fin.pos_iff_nonempty.2 ‹_›; positivity
  refine ⟨hw, ?_⟩
  simp only [planeProj]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem planeProj_self {y : Fin m → ℝ} (hy : y ∈ openSimplex m) : planeProj m y = y := by
  funext i; simp [planeProj, hy.2]

theorem isOpen_Uset : IsOpen (Uset m) := by
  have hc : Continuous (planeProj m) := contDiff_planeProj.continuous
  have : Uset m = ⋂ i, {w : Fin m → ℝ | 0 < planeProj m w i} := by
    ext w; simp [Uset]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ((continuous_apply i).comp hc)

theorem dot_Pl {v : Fin m → ℝ} (hv : ∑ i, v i = 0) (z : Fin m → ℝ) : v ⬝ᵥ Pl m z = v ⬝ᵥ z := by
  simp only [Pl, dotProduct, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    Pi.sub_apply, Lsum_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hv, zero_mul,
    sub_zero]

theorem V_lower (hf : IsRegularDensity f) [Nonempty (Fin m)] {y y' : Fin m → ℝ}
    (hy' : y' ∈ openSimplex m) : (y' - y) ⬝ᵥ psi f y ≤ Vf f y' - Vf f y := by
  have hC' := (psi_spec hf hy').1
  have := fenchel hf (psi f y') (psi f y)
  rw [hC'] at this
  simp only [Vf, sub_dotProduct]
  linarith

noncomputable def dotL (v : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => v ⬝ᵥ z
      map_add' := fun x y => dotProduct_add v x y
      map_smul' := fun c x => by simp [dotProduct_smul] }

theorem dotL_apply (v z : Fin m → ℝ) : dotL v z = v ⬝ᵥ z := rfl

noncomputable def dotLL (m : ℕ) : (Fin m → ℝ) →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := dotL
      map_add' := fun x y => by ext z; simp [dotL_apply, add_dotProduct]
      map_smul' := fun c x => by ext z; simp [dotL_apply, smul_dotProduct] }

theorem dotLL_apply (v z : Fin m → ℝ) : dotLL m v z = v ⬝ᵥ z := rfl

theorem abs_dot_le_norm (v d : Fin m → ℝ) : |v ⬝ᵥ d| ≤ m * (‖v‖ * ‖d‖) := by
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.univ, |v i * d i| ≤ ‖v‖ * ‖d‖ := fun i _ => by
    rw [abs_mul]
    have h1 := norm_le_pi_norm v i
    have h2 := norm_le_pi_norm d i
    rw [Real.norm_eq_abs] at h1 h2
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_sum this).trans ?_
  simp

theorem hasFDerivAt_W (hf : IsRegularDensity f) [Nonempty (Fin m)] {w : Fin m → ℝ}
    (hw : w ∈ Uset m) :
    HasFDerivAt (Vf f ∘ planeProj m) (dotLL m (psi f (planeProj m w))) w := by
  set q : (Fin m → ℝ) → (Fin m → ℝ) := fun x => psi f (planeProj m x) with hqdef
  have hqc : ContinuousAt q w :=
    ((psi_smooth hf (planeProj_mem hw)).1.continuousAt).comp
      (hasFDerivAt_planeProj w).continuousAt
  rw [hasFDerivAt_iff_tendsto]
  have hbound : ∀ᶠ x' in 𝓝 w, ‖x' - w‖⁻¹ * ‖(Vf f ∘ planeProj m) x' - (Vf f ∘ planeProj m) w -
      dotLL m (q w) (x' - w)‖ ≤ m * ‖q x' - q w‖ := by
    filter_upwards [isOpen_Uset.mem_nhds hw] with x' hx'
    have hy := planeProj_mem hw
    have hy' := planeProj_mem hx'
    have hdiff : planeProj m x' - planeProj m w = Pl m (x' - w) := by
      rw [planeProj_eq]; simp [map_sub]
    have hlow := V_lower hf (y := planeProj m w) hy'
    have hup := V_lower hf (y := planeProj m x') hy
    rw [hdiff, dotProduct_comm, dot_Pl (psi_spec hf hy).2] at hlow
    have e2 : planeProj m w - planeProj m x' = Pl m (w - x') := by
      rw [planeProj_eq]; simp [map_sub]
    rw [e2, dotProduct_comm, dot_Pl (psi_spec hf hy').2] at hup
    have e3 : psi f (planeProj m x') ⬝ᵥ (w - x') = -(psi f (planeProj m x') ⬝ᵥ (x' - w)) := by
      rw [← dotProduct_neg, neg_sub]
    rw [e3] at hup
    simp only [Function.comp_apply, dotLL_apply]
    set X := Vf f (planeProj m x') - Vf f (planeProj m w)
    have hX : |X - q w ⬝ᵥ (x' - w)| ≤ m * (‖q x' - q w‖ * ‖x' - w‖) := by
      have h4 := abs_dot_le_norm (q x' - q w) (x' - w)
      rw [sub_dotProduct] at h4
      rw [abs_le] at h4 ⊢
      simp only [hqdef] at h4 ⊢
      constructor <;> linarith [h4.1, h4.2]
    rw [Real.norm_eq_abs]
    by_cases hd : ‖x' - w‖ = 0
    · rw [hd, inv_zero, zero_mul]; positivity
    · have hdpos : 0 < ‖x' - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      rw [inv_mul_le_iff₀ hdpos]
      calc |X - q w ⬝ᵥ (x' - w)| ≤ m * (‖q x' - q w‖ * ‖x' - w‖) := hX
        _ = ‖x' - w‖ * (m * ‖q x' - q w‖) := by ring
  have hlim : Tendsto (fun x' => (m : ℝ) * ‖q x' - q w‖) (𝓝 w) (𝓝 0) := by
    have h1 : Tendsto (fun x' => q x' - q w) (𝓝 w) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.2 hqc.tendsto
    have h2 := (h1.norm).const_mul (m : ℝ)
    simpa using h2
  exact squeeze_zero' (Eventually.of_forall fun _ => by positivity) hbound hlim

theorem fderiv_W (hf : IsRegularDensity f) [Nonempty (Fin m)] {w : Fin m → ℝ}
    (hw : w ∈ Uset m) :
    fderiv ℝ (Vf f ∘ planeProj m) w = dotLL m (psi f (planeProj m w)) :=
  (hasFDerivAt_W hf hw).fderiv

theorem W_contDiffOn (hf : IsRegularDensity f) [Nonempty (Fin m)] :
    ContDiffOn ℝ 2 (Vf f ∘ planeProj m) (Uset m) := by
  have hUo : IsOpen (Uset m) := isOpen_Uset
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hUo]
  refine ⟨fun w hw => (hasFDerivAt_W hf hw).differentiableAt.differentiableWithinAt,
    fun h => absurd h (by decide), ?_⟩
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  have hq : ContDiffAt ℝ 1 (fun x => psi f (planeProj m x)) w :=
    (psi_smooth hf (planeProj_mem hw)).1.comp w contDiff_planeProj.contDiffAt
  have h1 : ContDiffAt ℝ 1 (fun x => dotLL m (psi f (planeProj m x))) w :=
    (dotLL m).contDiff.contDiffAt.comp w hq
  exact h1.congr_of_eventuallyEq
    (Filter.eventually_of_mem (hUo.mem_nhds hw) fun x hx => fderiv_W hf hx)

theorem W_pd (hf : IsRegularDensity f) [Nonempty (Fin m)] {y : Fin m → ℝ}
    (hy : y ∈ openSimplex m) (z : Fin m → ℝ) (hz : ∑ i, z i = 0) (hz0 : z ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (Vf f ∘ planeProj m)) y z z := by
  have hyU : y ∈ Uset m := by
    show ∀ i, 0 < planeProj m y i
    rw [planeProj_self hy]; exact hy.1
  have hUo : IsOpen (Uset m) := isOpen_Uset
  have hev : fderiv ℝ (Vf f ∘ planeProj m) =ᶠ[𝓝 y] fun w => dotLL m (psi f (planeProj m w)) :=
    Filter.eventually_of_mem (hUo.mem_nhds hyU) fun x hx => fderiv_W hf hx
  rw [hev.fderiv_eq]
  set E := DPhiE hf (psi f y) with hE
  have hψd : HasFDerivAt (psi f) (E.symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (planeProj m y) := by
    rw [planeProj_self hy]; exact (psi_smooth hf hy).2
  have hq := hψd.comp y (hasFDerivAt_planeProj y)
  have hfull := (dotLL m).hasFDerivAt.comp y hq
  rw [show (fun w => dotLL m (psi f (planeProj m w))) = ⇑(dotLL m) ∘ psi f ∘ planeProj m from rfl,
    hfull.fderiv]
  simp only [ContinuousLinearMap.comp_apply, dotLL_apply]
  have hPz : Pl m z = z := by
    funext i
    simp [Pl, Lsum_apply, hz]
  rw [hPz]
  set u := E.symm z with hu
  have hEu : DPhi f (psi f y) u = z := by
    rw [← DPhiE_coe hf, hu]
    exact E.apply_symm_apply z
  have hsu : ∑ j, u j = 0 := by
    rw [← DPhi_sum hf (psi f y) u, hEu, hz]
  have hL : Lsum m u = 0 := by funext i; simp [Lsum_apply, hsu]
  have hDu : fderiv ℝ (choiceProb f) (psi f y) u = z := by
    have := hEu
    simp only [DPhi, ContinuousLinearMap.add_apply, hL, add_zero] at this
    exact this
  have hu0 : u ≠ 0 := by
    intro h0
    apply hz0
    rw [← hEu, h0, map_zero]
  have := dC_pos hf (psi f y) u hsu hu0
  rw [hDu, dotProduct_comm] at this
  exact this

theorem W_blowup (hf : IsRegularDensity f) [Nonempty (Fin m)] (M : ℝ) :
    ∃ δ > 0, ∀ y ∈ openSimplex m, (∃ i, y i < δ) →
      M < ‖fderiv ℝ (Vf f ∘ planeProj m) y‖ := by
  set M' := max M 0 with hM'
  have hK : IsCompact (Metric.closedBall (0 : Fin m → ℝ) M') := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : Fin m → ℝ) M').Nonempty :=
    ⟨0, Metric.mem_closedBall_self (le_max_right _ _)⟩
  have hC := continuous_choiceProb hf
  have hδi : ∀ i : Fin m, ∃ d > 0, ∀ π ∈ Metric.closedBall (0 : Fin m → ℝ) M',
      d ≤ choiceProb f π i := by
    intro i
    obtain ⟨π0, -, hmin⟩ := hK.exists_isMinOn hne ((continuous_apply i).comp hC).continuousOn
    exact ⟨choiceProb f π0 i, choiceProb_pos hf π0 i, fun π hπ => hmin hπ⟩
  choose d hd hdle using hδi
  refine ⟨Finset.univ.inf' Finset.univ_nonempty d,
    (Finset.lt_inf'_iff _).2 fun i _ => hd i, ?_⟩
  rintro y hy ⟨i, hi⟩
  by_contra hcon
  push_neg at hcon
  have hyU : y ∈ Uset m := by
    show ∀ i, 0 < planeProj m y i
    rw [planeProj_self hy]; exact hy.1
  rw [fderiv_W hf hyU, planeProj_self hy] at hcon
  have hcoord : ∀ j, |psi f y j| ≤ M' := by
    intro j
    have h1 := (dotLL m (psi f y)).le_opNorm (Pi.single j 1)
    have h2 : ‖(Pi.single j (1 : ℝ) : Fin m → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
        by_cases h : k = j
        · subst h; simp
        · simp [Pi.single_apply, h]
    have h3 : dotLL m (psi f y) (Pi.single j 1) = psi f y j := by
      rw [dotLL_apply, dotProduct_single, mul_one]
    rw [h3, Real.norm_eq_abs] at h1
    have h4 : ‖dotLL m (psi f y)‖ * ‖(Pi.single j (1 : ℝ) : Fin m → ℝ)‖ ≤
        ‖dotLL m (psi f y)‖ := mul_le_of_le_one_right (norm_nonneg _) h2
    have := le_max_left M 0
    linarith
  have hmem : psi f y ∈ Metric.closedBall (0 : Fin m → ℝ) M' := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => by
      rw [Real.norm_eq_abs]; exact hcoord j
  have h5 := hdle i _ hmem
  rw [(psi_spec hf hy).1] at h5
  have h6 := Finset.inf'_le d (Finset.mem_univ i)
  linarith

theorem main_rep (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) :
    ∃ V : (Fin m → ℝ) → ℝ, IsAdmissible V ∧ IsPerturbedArgmax V (choiceProb f) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨Vf f, ⟨W_contDiffOn hf, fun y hy z hz hz0 => W_pd hf hy z hz hz0,
    fun M => W_blowup hf M⟩, argmax_of hf (Vf f) fun y hy => ⟨psi f y, (psi_spec hf hy).1, rfl⟩⟩

end StochFictPlay.ZeroSumESS.AuxD555

namespace StochFictPlay.DiscreteChoice.AdaptD555

open StochFictPlay.DiscreteChoice

theorem choiceProb_eq' {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    choiceProb f = StochFictPlay.ZeroSumESS.choiceProb (fun x => ENNReal.ofReal (f x)) := by
  funext π i; rfl

theorem regular {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) :
    StochFictPlay.ZeroSumESS.IsRegularDensity (fun x => ENNReal.ofReal (f x)) := by
  refine ⟨ENNReal.continuous_ofReal.comp hf.continuous, fun e => ENNReal.ofReal_pos.2 (hf.pos e),
    fun e => ENNReal.ofReal_ne_top, hf.lintegral_eq_one, ?_⟩
  rw [← choiceProb_eq']; exact hC

theorem planeProj_of_sum {n : ℕ} {w : Fin n → ℝ} (h : ∑ i, w i = 1) :
    StochFictPlay.ZeroSumESS.planeProj n w = w := by
  funext i; simp [StochFictPlay.ZeroSumESS.planeProj, h]

theorem hess_comp {n : ℕ} (F : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (hF : ContDiffAt ℝ 2 F y)
    (w : tangentSpace n) :
    fderiv ℝ (fderiv ℝ (fun z : tangentSpace n => F (y + (z : Fin n → ℝ)))) 0 w w =
      fderiv ℝ (fderiv ℝ F) y (w : Fin n → ℝ) (w : Fin n → ℝ) := by
  set L : tangentSpace n →L[ℝ] (Fin n → ℝ) := (tangentSpace n).subtypeL with hL
  have hA : ∀ z : tangentSpace n,
      HasFDerivAt (fun z : tangentSpace n => y + (z : Fin n → ℝ)) L z :=
    fun z => L.hasFDerivAt.const_add y
  have hcont : Continuous (fun z : tangentSpace n => y + (z : Fin n → ℝ)) :=
    continuous_const.add continuous_subtype_val
  have hev : ∀ᶠ x in 𝓝 y, DifferentiableAt ℝ F x :=
    (hF.eventually (by decide)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev0 : ∀ᶠ z : tangentSpace n in 𝓝 0, DifferentiableAt ℝ F (y + (z : Fin n → ℝ)) := by
    have := (hcont.continuousAt (x := 0)).tendsto
    simp only [Submodule.coe_zero, add_zero] at this
    exact this.eventually hev
  have hfd : fderiv ℝ (fun z : tangentSpace n => F (y + (z : Fin n → ℝ))) =ᶠ[𝓝 0]
      fun z : tangentSpace n => (fderiv ℝ F (y + (z : Fin n → ℝ))).comp L :=
    hev0.mono fun z hz => (hz.hasFDerivAt.comp z (hA z)).fderiv
  rw [hfd.fderiv_eq]
  have hD : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun z : tangentSpace n => fderiv ℝ F (y + (z : Fin n → ℝ)))
      ((fderiv ℝ (fderiv ℝ F) y).comp L) 0 := by
    have h0 : y + ((0 : tangentSpace n) : Fin n → ℝ) = y := by simp
    have hD' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y)
        (y + ((0 : tangentSpace n) : Fin n → ℝ)) := by rw [h0]; exact hD.hasFDerivAt
    exact hD'.comp (0 : tangentSpace n) (hA 0)
  have h2 : HasFDerivAt (fun z : tangentSpace n => (fderiv ℝ F (y + (z : Fin n → ℝ))).comp L)
      _ (0 : tangentSpace n) := h1.clm_comp (hasFDerivAt_const L (0 : tangentSpace n))
  rw [h2.fderiv]
  simp [L]

theorem main {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (hC : ContDiff ℝ 1 (choiceProb f)) :
    ∃ V : (Fin n → ℝ) → ℝ, IsAdmissible V ∧
      ∀ π : Fin n → ℝ, choiceProb f π ∈ openSimplex n ∧
        ∀ y ∈ openSimplex n, y ≠ choiceProb f π →
          y ⬝ᵥ π - V y < choiceProb f π ⬝ᵥ π - V (choiceProb f π) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f' : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hf'
  have hr : StochFictPlay.ZeroSumESS.IsRegularDensity f' := regular f hf hC
  have hCe : choiceProb f = StochFictPlay.ZeroSumESS.choiceProb f' := choiceProb_eq' f
  set V := StochFictPlay.ZeroSumESS.AuxD555.Vf f' with hV
  set F := V ∘ StochFictPlay.ZeroSumESS.planeProj n with hF
  have hUo := @StochFictPlay.ZeroSumESS.AuxD555.isOpen_Uset n
  have hyU : ∀ y ∈ openSimplex n, y ∈ StochFictPlay.ZeroSumESS.AuxD555.Uset n := fun y hy => by
    show ∀ i, 0 < StochFictPlay.ZeroSumESS.planeProj n y i
    rw [planeProj_of_sum hy.2]; exact hy.1
  have hC2 : ∀ y ∈ openSimplex n, ContDiffAt ℝ 2 F y := fun y hy =>
    (StochFictPlay.ZeroSumESS.AuxD555.W_contDiffOn hr).contDiffAt (hUo.mem_nhds (hyU y hy))
  have hR : ∀ y ∈ openSimplex n,
      planeRestrict V y = fun z : tangentSpace n => F (y + (z : Fin n → ℝ)) := by
    intro y hy; funext z
    have hs : ∑ i, (y + (z : Fin n → ℝ)) i = 1 := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, hy.2, (mem_tangentSpace.1 z.2), add_zero]
    simp only [planeRestrict, hF, Function.comp_apply, planeProj_of_sum hs]
  refine ⟨V, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    rw [hR y hy]
    have hA : ContDiff ℝ 2 (fun z : tangentSpace n => y + (z : Fin n → ℝ)) :=
      contDiff_const.add (tangentSpace n).subtypeL.contDiff
    have h0 : y + ((0 : tangentSpace n) : Fin n → ℝ) = y := by simp
    have h2 : ContDiffAt ℝ 2 F (y + ((0 : tangentSpace n) : Fin n → ℝ)) := by
      rw [h0]; exact hC2 y hy
    exact ContDiffAt.comp (g := F) (0 : tangentSpace n) h2 hA.contDiffAt
  · intro y hy w hw
    rw [hR y hy, hess_comp F y (hC2 y hy) w]
    have hs : ∑ i, (w : Fin n → ℝ) i = 0 := mem_tangentSpace.1 w.2
    have hw0 : (w : Fin n → ℝ) ≠ 0 := fun h => hw (Subtype.ext h)
    exact StochFictPlay.ZeroSumESS.AuxD555.W_pd hr hy _ hs hw0
  · intro M
    obtain ⟨δ, hδ, hb⟩ := StochFictPlay.ZeroSumESS.AuxD555.W_blowup hr (M * n)
    refine ⟨δ, hδ, fun y hy hi g hg => ?_⟩
    have hb' := hb y hy hi
    have hpsi := StochFictPlay.ZeroSumESS.AuxD555.psi_spec hr hy
    rw [StochFictPlay.ZeroSumESS.AuxD555.fderiv_W hr (hyU y hy), planeProj_of_sum hy.2] at hb'
    set p := StochFictPlay.ZeroSumESS.AuxD555.psi f' y with hp
    have hdir : ∀ z : Fin n → ℝ, ∑ i, z i = 0 → g ⬝ᵥ z = p ⬝ᵥ z := by
      intro z hz
      have hgz := hg.2 z hz
      have hW := StochFictPlay.ZeroSumESS.AuxD555.hasFDerivAt_W hr (hyU y hy)
      rw [planeProj_of_sum hy.2] at hW
      have hW' : HasFDerivAt F (StochFictPlay.ZeroSumESS.AuxD555.dotLL n p)
          (y + (0 : ℝ) • z) := by simpa using hW
      have hline : HasDerivAt (fun h : ℝ => y + h • z) z 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add y
      have hcomp := hW'.comp_hasDerivAt (0 : ℝ) hline
      have heq : (F ∘ fun h : ℝ => y + h • z) = fun h : ℝ => V (y + h • z) := by
        funext h
        have hs : ∑ i, (y + h • z) i = 1 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, hy.2, hz, mul_zero, add_zero]
        simp only [hF, Function.comp_apply, planeProj_of_sum hs]
      rw [heq] at hcomp
      have := hgz.unique hcomp
      rw [this, StochFictPlay.ZeroSumESS.AuxD555.dotLL_apply]
    have hgp : g = p := by
      have hd : ∑ i, (g - p) i = 0 := by
        simp [Finset.sum_sub_distrib, hg.1, hpsi.2]
      have h0 : (g - p) ⬝ᵥ (g - p) = 0 := by rw [sub_dotProduct, hdir _ hd, sub_self]
      exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h0)
    have hnorm : ‖StochFictPlay.ZeroSumESS.AuxD555.dotLL n p‖ ≤ n * ‖p‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
        rw [StochFictPlay.ZeroSumESS.AuxD555.dotLL_apply, Real.norm_eq_abs]
        exact (StochFictPlay.ZeroSumESS.AuxD555.abs_dot_le_norm p v).trans (le_of_eq (by ring))
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [hgp]
    by_contra hcon
    push_neg at hcon
    have : M * n < n * ‖p‖ := lt_of_lt_of_le hb' hnorm
    nlinarith
  · intro π
    have := StochFictPlay.ZeroSumESS.AuxD555.argmax_of hr V (fun y hy =>
      ⟨StochFictPlay.ZeroSumESS.AuxD555.psi f' y,
        (StochFictPlay.ZeroSumESS.AuxD555.psi_spec hr hy).1, rfl⟩) π
    rw [hCe]; exact this

end StochFictPlay.DiscreteChoice.AdaptD555

open StochFictPlay.DiscreteChoice in
theorem solution {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (hC : ContDiff ℝ 1 (choiceProb f)) :
    ∃ V : (Fin n → ℝ) → ℝ, IsAdmissible V ∧
      ∀ π : Fin n → ℝ, choiceProb f π ∈ openSimplex n ∧
        ∀ y ∈ openSimplex n, y ≠ choiceProb f π →
          y ⬝ᵥ π - V y < choiceProb f π ⬝ᵥ π - V (choiceProb f π) := by
  exact StochFictPlay.DiscreteChoice.AdaptD555.main hn f hf hC
