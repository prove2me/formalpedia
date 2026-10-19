-- Prove2me | solution 1 for StochFictPlay.Potential.lemmaA4_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T08:00:51.127017+00:00
-- url     : https://prove2.me/submissions/45085da1-8cf6-4d24-8b48-7d9837839d59

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Stability
import Definitions.Def_StochFictPlay_Potential_PotentialGame

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochFictPlay.Potential.Aux22

open StochFictPlay.Potential

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
  have hfm : Measurable f := hf.1
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

/-- equality in the subgradient inequality forces the choice probabilities to be ordered. -/
theorem strict_aux (hf : IsRegularDensity f) [Nonempty (Fin m)] (π π' : Fin m → ℝ)
    (h : G f π' - G f π ≤ choiceProb f π ⬝ᵥ (π' - π)) (i : Fin m) :
    choiceProb f π i ≤ choiceProb f π' i := by
  have := isProb hf
  set g : (Fin m → ℝ) → ℝ := fun e => ∑ i, (Ev π i).indicator (fun _ => π' i - π i) e with hg
  have hgi : ∀ i, Integrable ((Ev π i).indicator (fun _ : Fin m → ℝ => π' i - π i)) (μf f) :=
    fun i => (integrable_const _).indicator (measurableSet_Ev π i)
  have hint : ∫ e, g e ∂(μf f) = choiceProb f π ⬝ᵥ (π' - π) := by
    rw [hg, integral_finsetSum _ (fun i _ => hgi i)]
    simp only [dotProduct, choiceProb_eq, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (measurableSet_Ev π i), smul_eq_mul]
  have hgint : Integrable g (μf f) := integrable_finsetSum _ (fun i _ => hgi i)
  have hFi : Integrable (fun e => (phi π' e - phi π e) - g e) (μf f) :=
    ((integrable_phi hf π').sub (integrable_phi hf π)).sub hgint
  have hgv : ∀ e i, e ∈ Ev π i → g e = π' i - π i := by
    intro e i hi
    rw [hg]
    simp only
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hi]
    · intro j _ hji
      rw [Set.indicator_of_notMem]
      intro hj
      exact Ev_disjoint π hji e hj hi
    · simp
  have hF0 : 0 ≤ᵐ[μf f] (fun e => (phi π' e - phi π e) - g e) := by
    filter_upwards [ae_exists_Ev hf π] with e he
    obtain ⟨i, hi⟩ := he
    simp only [Pi.zero_apply, sub_nonneg]
    rw [hgv e i hi]
    simp only [phi]
    rw [smax_of_Ev hi]
    have := le_smax (fun j => π' j + e j) i
    linarith
  have hFint : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) =
      G f π' - G f π - choiceProb f π ⬝ᵥ (π' - π) := by
    have e1 : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) =
        ∫ e, (phi π' e - phi π e) ∂(μf f) - ∫ e, g e ∂(μf f) :=
      integral_sub (f := fun e => phi π' e - phi π e) (g := g)
        ((integrable_phi hf π').sub (integrable_phi hf π)) hgint
    have e2 : ∫ e, (phi π' e - phi π e) ∂(μf f) =
        ∫ e, phi π' e ∂(μf f) - ∫ e, phi π e ∂(μf f) :=
      integral_sub (integrable_phi hf π') (integrable_phi hf π)
    rw [e1, e2, hint]
    rfl
  have h0 : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) = 0 :=
    le_antisymm (by rw [hFint]; linarith) (integral_nonneg_of_ae hF0)
  have hF : (fun e => (phi π' e - phi π e) - g e) =ᵐ[μf f] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hF0 hFi).1 h0
  have hae : Ev π i ≤ᵐ[μf f] Ev π' i := by
    filter_upwards [hF, ae_exists_Ev hf π'] with e hFe he2 hei
    obtain ⟨j, hj⟩ := he2
    simp only [Pi.zero_apply] at hFe
    rw [hgv e i hei] at hFe
    simp only [phi] at hFe
    rw [smax_of_Ev hj] at hFe
    have hsm : smax (fun l => π l + e l) = π i + e i := smax_of_Ev hei
    rw [hsm] at hFe
    by_cases hji : j = i
    · rw [← hji]; exact hj
    · exfalso
      have := hj i (Ne.symm hji)
      linarith
  rw [choiceProb_eq, choiceProb_eq, Measure.real, Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)

/-! ### conditional mean of the argmax choice -/

theorem measurable_argmaxVec_apply {k : ℕ} (i : Fin k) :
    Measurable (fun v : Fin k → ℝ => argmaxVec v i) := by
  have hset : MeasurableSet {v : Fin k → ℝ | (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i)} := by
    have h1 : {v : Fin k → ℝ | (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i)} =
        (⋂ j, {v : Fin k → ℝ | v j ≤ v i}) ∩
          ⋂ j, ⋂ (_ : j < i), {v : Fin k → ℝ | v j < v i} := by
      ext v; simp
    rw [h1]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.iInter fun j =>
        measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)
    · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  unfold argmaxVec
  exact Measurable.ite hset measurable_const measurable_const

theorem argmaxVec_eq_indicator {m : ℕ} (π e : Fin m → ℝ) (k0 i0 : Fin m) (h : e ∈ Ev π i0) :
    argmaxVec (fun k => π k + e k) k0 = (Ev π k0).indicator (fun _ => (1 : ℝ)) e := by
  unfold argmaxVec
  by_cases hk : k0 = i0
  · subst hk
    rw [Set.indicator_of_mem h, if_pos]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_cases hj : j = k0
      · subst hj; exact le_rfl
      · exact (h j hj).le
    · exact h j (ne_of_lt hj)
  · rw [Set.indicator_of_notMem (fun hk0 => Ev_disjoint π hk e hk0 h), if_neg]
    rintro ⟨h1, -⟩
    have := h1 i0
    have := h k0 hk
    simp only at *
    linarith

theorem integral_argmaxVec (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ)
    (k0 : Fin m) :
    ∫ e, argmaxVec (fun k => π k + e k) k0 ∂(μf f) = choiceProb f π k0 := by
  have := isProb hf
  have hae : (fun e => argmaxVec (fun k => π k + e k) k0) =ᵐ[μf f]
      (Ev π k0).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_exists_Ev hf π] with e he
    obtain ⟨i0, hi0⟩ := he
    exact argmaxVec_eq_indicator π e k0 i0 hi0
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_Ev π k0), smul_eq_mul,
    mul_one, choiceProb_eq]

theorem cm_argmax (hf : IsRegularDensity f) [Nonempty (Fin m)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → (Fin m → ℝ)) (hξ : Measurable ξ) (hlaw : P.map ξ = μf f)
    {H : Type*} [MeasurableSpace H] (w : Ω → ℝ × H) (hw : Measurable w)
    (hind : IndepFun w ξ P) (hb : ∀ ω, |(w ω).1| ≤ 1)
    (g : H → (Fin m → ℝ)) (hg : Measurable g) (k0 : Fin m) :
    ∫ ω, (w ω).1 * argmaxVec (fun k => g (w ω).2 k + ξ ω k) k0 ∂P =
      ∫ ω, (w ω).1 * choiceProb f (g (w ω).2) k0 ∂P := by
  have := isProb hf
  set κ : (ℝ × H) × (Fin m → ℝ) → ℝ :=
    fun q => q.1.1 * argmaxVec (fun k => g q.1.2 k + q.2 k) k0 with hκ
  have hκm : Measurable κ := by
    refine (measurable_fst.comp measurable_fst).mul ?_
    refine (measurable_argmaxVec_apply k0).comp ?_
    refine measurable_pi_lambda _ (fun k => ?_)
    exact ((measurable_pi_apply k).comp (hg.comp (measurable_snd.comp measurable_fst))).add
      (measurable_pi_apply k |>.comp measurable_snd)
  have hprod : P.map (fun ω => (w ω, ξ ω)) = (P.map w).prod (P.map ξ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hw.aemeasurable hξ.aemeasurable).1 hind
  have hpm : Measurable (fun ω => (w ω, ξ ω)) := hw.prodMk hξ
  have hbκ : ∀ q : (ℝ × H) × (Fin m → ℝ), |q.1.1| ≤ 1 → |κ q| ≤ 1 := by
    intro q hq
    simp only [hκ]
    rw [abs_mul]
    have h1 : |argmaxVec (fun k => g q.1.2 k + q.2 k) k0| ≤ 1 := by
      unfold argmaxVec; split_ifs <;> simp
    nlinarith [abs_nonneg q.1.1, abs_nonneg (argmaxVec (fun k => g q.1.2 k + q.2 k) k0)]
  -- left side as an integral over the product
  have hL : ∫ ω, (w ω).1 * argmaxVec (fun k => g (w ω).2 k + ξ ω k) k0 ∂P =
      ∫ q, κ q ∂((P.map w).prod (P.map ξ)) := by
    rw [← hprod, integral_map hpm.aemeasurable hκm.aestronglyMeasurable]
  have hint : Integrable κ ((P.map w).prod (P.map ξ)) := by
    rw [← hprod, integrable_map_measure hκm.aestronglyMeasurable hpm.aemeasurable]
    refine Integrable.of_bound (hκm.comp hpm).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hbκ _ (hb ω)
  rw [hL, integral_prod _ hint]
  simp_rw [hlaw]
  have hinner : ∀ a : ℝ × H, ∫ e, κ (a, e) ∂(μf f) = a.1 * choiceProb f (g a.2) k0 := by
    intro a
    simp only [hκ]
    rw [integral_const_mul, integral_argmaxVec hf (g a.2) k0]
  simp_rw [hinner]
  rw [integral_map hw.aemeasurable]
  exact (measurable_fst.mul ((measurable_pi_apply k0).comp (continuous_choiceProb hf).measurable
    |>.comp (hg.comp measurable_snd))).aestronglyMeasurable

end StochFictPlay.Potential.Aux22

/-! ## K2d: Lemma A.4 (Pemantle nondegeneracy of standard SFP) -/

universe v

namespace StochFictPlay.Potential.K2d

open StochFictPlay.Potential StochFictPlay.Potential.Aux22

variable {p : ℕ} {n : Fin p → ℕ}

theorem le_one_of_mem_stdSimplex {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ stdSimplex ℝ (Fin m))
    (i : Fin m) : x i ≤ 1 := by
  have h0 := hx.1
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
    _ = 1 := hx.2

theorem abs_payoffVec_le (u : (α : Fin p) → Profile n → ℝ) {z : Mixed n}
    (hz : z ∈ mixedProfiles n) (α : Fin p) (k : Fin (n α)) :
    |payoffVec u z α k| ≤ ∑ s : Profile n, |u α s| := by
  unfold payoffVec
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  split_ifs
  · rw [abs_mul]
    have hp : |∏ β ∈ Finset.univ.erase α, z β (s β)| ≤ 1 := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun β _ => abs_nonneg _) (fun β _ => ?_)
      have hzb : z β ∈ stdSimplex ℝ (Fin (n β)) := hz β
      rw [abs_of_nonneg (hzb.1 _)]
      exact le_one_of_mem_stdSimplex hzb _
    nlinarith [abs_nonneg (u α s), abs_nonneg (∏ β ∈ Finset.univ.erase α, z β (s β))]
  · simp

/-- shocks favouring `i` by more than `2B` -/
def Obig {m : ℕ} (B : ℝ) (i : Fin m) : Set (Fin m → ℝ) := {e | ∀ j, j ≠ i → e j + 2 * B < e i}

theorem isOpen_Obig {m : ℕ} (B : ℝ) (i : Fin m) : IsOpen (Obig B i) := by
  have : Obig B i = ⋂ j ∈ (Finset.univ.erase i), {e : Fin m → ℝ | e j + 2 * B < e i} := by
    ext e
    simp only [Obig, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [this]
  exact isOpen_biInter_finset fun j _ =>
    isOpen_lt ((continuous_apply j).add continuous_const) (continuous_apply i)

theorem Obig_nonempty {m : ℕ} (B : ℝ) (i : Fin m) : (Obig B i).Nonempty := by
  refine ⟨fun j => if j = i then 2 * |B| + 1 else 0, fun j hj => ?_⟩
  show (if j = i then 2 * |B| + 1 else 0) + 2 * B < (if i = i then 2 * |B| + 1 else 0)
  rw [if_neg hj, if_pos rfl]
  have := le_abs_self B
  linarith

theorem Obig_sub_Ev {m : ℕ} {B : ℝ} {π : Fin m → ℝ} (hπ : ∀ k, |π k| ≤ B) (i : Fin m) :
    Obig B i ⊆ Ev π i := by
  intro e he j hj
  have h0 := he j hj
  have h1 := abs_le.mp (hπ j)
  have h2 := abs_le.mp (hπ i)
  linarith [h1.1, h1.2, h2.1, h2.2]

theorem argmaxVec_of_Ev {m : ℕ} {π e : Fin m → ℝ} {i : Fin m} (h : e ∈ Ev π i) :
    argmaxVec (fun k => π k + e k) = Pi.single i 1 := by
  funext k0
  rw [argmaxVec_eq_indicator π e k0 i h]
  by_cases hk : k0 = i
  · subst hk; rw [Set.indicator_of_mem h, Pi.single_eq_same]
  · rw [Set.indicator_of_notMem (fun hk0 => Ev_disjoint π hk e hk0 h), Pi.single_eq_of_ne hk]

theorem sfpChoice_eq_pureVec {Ω : Type*} (u : (α : Fin p) → Profile n → ℝ) {z : Mixed n}
    (hz : z ∈ mixedProfiles n) (εt : (α : Fin p) → Ω → (Fin (n α) → ℝ)) (s : Profile n) {ω : Ω}
    (hω : ∀ α, εt α ω ∈ Obig (∑ s' : Profile n, |u α s'|) (s α)) :
    sfpChoice u z εt ω = pureVec s := by
  funext α
  show argmaxVec (fun k => payoffVec u z α k + εt α ω k) = Pi.single (s α) (1 : ℝ)
  exact argmaxVec_of_Ev (Obig_sub_Ev (fun k => abs_payoffVec_le u hz α k) (s α) (hω α))

theorem prob_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞} {ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)}
    (hε : IsShockFamily P f ε) (t : ℕ) (O : (α : Fin p) → Set (Fin (n α) → ℝ))
    (hO : ∀ α, MeasurableSet (O α)) :
    P {ω | ∀ α, ε t α ω ∈ O α} = ∏ α, μf (f α) (O α) := by
  have hind := hε.2.2
  set emb : Fin p ↪ ℕ × Fin p := ⟨fun α => (t, α), fun a b h => (Prod.mk.inj h).2⟩ with hemb
  set S : Finset (ℕ × Fin p) := Finset.univ.map emb with hS
  have h := hind.measure_inter_preimage_eq_mul S (sets := fun i => O i.2) (fun i _ => hO i.2)
  have hset : (⋂ i ∈ S, (fun ω => ε i.1 i.2 ω) ⁻¹' (fun i : ℕ × Fin p => O i.2) i) =
      {ω | ∀ α, ε t α ω ∈ O α} := by
    ext ω
    simp only [hS, hemb, Set.mem_iInter, Set.mem_preimage, Finset.mem_map, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk, Set.mem_ofPred_eq]
    constructor
    · intro hh α; exact hh (t, α) ⟨α, rfl⟩
    · rintro hh _ ⟨α, rfl⟩; exact hh α
  rw [hset] at h
  rw [h, Finset.prod_map]
  refine Finset.prod_congr rfl fun α _ => ?_
  show P ((ε t α) ⁻¹' O α) = μf (f α) (O α)
  rw [← Measure.map_apply (hε.1 t α) (hO α), hε.2.1 t α]

theorem measurable_choice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞} {ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)}
    (hε : IsShockFamily P f ε) (u : (α : Fin p) → Profile n → ℝ) (z : Mixed n) (t : ℕ)
    (α : Fin p) (k : Fin (n α)) : Measurable (fun ω => sfpChoice u z (ε t) ω α k) :=
  (measurable_argmaxVec_apply k).comp (measurable_pi_lambda _ fun k' =>
    measurable_const.add ((measurable_pi_apply k').comp (hε.1 t α)))

theorem abs_choice_le {Ω : Type*} (u : (α : Fin p) → Profile n → ℝ) (z : Mixed n)
    (εt : (α : Fin p) → Ω → (Fin (n α) → ℝ)) (ω : Ω) (α : Fin p) (k : Fin (n α)) :
    |sfpChoice u z εt ω α k| ≤ 1 := by
  show |argmaxVec (fun k' => payoffVec u z α k' + εt α ω k') k| ≤ 1
  unfold argmaxVec; split_ifs <;> simp

theorem integral_choice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞} {ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)}
    (hf : ∀ α, IsRegularDensity (f α)) (hn : ∀ α, 1 ≤ n α) (hε : IsShockFamily P f ε)
    (u : (α : Fin p) → Profile n → ℝ) (z : Mixed n) (t : ℕ) (α : Fin p) (k : Fin (n α)) :
    ∫ ω, sfpChoice u z (ε t) ω α k ∂P = pbr f u z α k := by
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  have hm : Measurable (fun e : Fin (n α) → ℝ => argmaxVec (fun k' => payoffVec u z α k' + e k') k) :=
    (measurable_argmaxVec_apply k).comp
      (measurable_pi_lambda _ fun k' => measurable_const.add (measurable_pi_apply k'))
  show ∫ ω, argmaxVec (fun k' => payoffVec u z α k' + ε t α ω k') k ∂P =
    choiceProb (f α) (payoffVec u z α) k
  have hlaw : μf (f α) = P.map (ε t α) := (hε.2.1 t α).symm
  rw [← integral_argmaxVec (hf α) (payoffVec u z α) k, hlaw,
    integral_map (hε.1 t α).aemeasurable hm.aestronglyMeasurable]

/-- a unit tangent vector is not almost constant on pure profiles -/
theorem exists_profile_large (hn : ∀ α, 1 ≤ n α) {θ : Mixed n} (hθ : θ ∈ unitTangent n)
    (K : Fin p → ℝ) (hN : 0 < ∑ α, n α) :
    ∃ s : Profile n, 1 / (4 * ((∑ α, n α : ℕ) : ℝ)) ≤ |∑ α, (θ α (s α) - K α)| := by
  classical
  set N : ℝ := ((∑ α, n α : ℕ) : ℝ) with hNdef
  have hNp : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hN
  set c1 : ℝ := 1 / (4 * N) with hc1
  have hc1p : 0 < c1 := by positivity
  by_contra hne
  push Not at hne
  set s0 : Profile n := fun β => ⟨0, hn β⟩ with hs0
  set y : Profile n → ℝ := fun s => ∑ α, (θ α (s α) - K α) with hy
  have hdiff : ∀ α (i i' : Fin (n α)),
      y (Function.update s0 α i) - y (Function.update s0 α i') = θ α i - θ α i' := by
    intro α i i'
    simp only [hy]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single α]
    · simp [Function.update_self]
    · intro β _ hβ
      simp [Function.update_of_ne hβ]
    · intro h; exact absurd (Finset.mem_univ α) h
  have hpair : ∀ α (i i' : Fin (n α)), |θ α i - θ α i'| ≤ 2 * c1 := by
    intro α i i'
    rw [← hdiff]
    have h1 := hne (Function.update s0 α i)
    have h2 := hne (Function.update s0 α i')
    calc |y (Function.update s0 α i) - y (Function.update s0 α i')| ≤
        |y (Function.update s0 α i)| + |y (Function.update s0 α i')| := abs_sub _ _
      _ ≤ 2 * c1 := by simp only [hy]; linarith
  have hθt : ∀ α, ∑ i, θ α i = 0 := hθ.1
  have hsingle : ∀ α (i : Fin (n α)), |θ α i| ≤ 2 * c1 := by
    intro α i
    have hnα : (0 : ℝ) < n α := by exact_mod_cast hn α
    have hsum : (n α : ℝ) * θ α i = ∑ i', (θ α i - θ α i') := by
      rw [Finset.sum_sub_distrib, hθt α, sub_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have : (n α : ℝ) * |θ α i| ≤ (n α : ℝ) * (2 * c1) := by
      calc (n α : ℝ) * |θ α i| = |(n α : ℝ) * θ α i| := by
            rw [abs_mul, abs_of_pos hnα]
        _ = |∑ i', (θ α i - θ α i')| := by rw [hsum]
        _ ≤ ∑ i', |θ α i - θ α i'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i' : Fin (n α), 2 * c1 := Finset.sum_le_sum fun i' _ => hpair α i i'
        _ = (n α : ℝ) * (2 * c1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_mul_le_mul_left this hnα
  have hsq : ∑ α, ∑ i, θ α i ^ 2 ≤ ∑ α, ∑ _i : Fin (n α), (2 * c1) ^ 2 :=
    Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hsingle α i) 2
  have hR : ∑ α, ∑ _i : Fin (n α), (2 * c1) ^ 2 = N * (2 * c1) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hNdef, ← Finset.sum_mul]; push_cast; ring
  have hval : N * (2 * c1) ^ 2 = 1 / (4 * N) := by rw [hc1]; field_simp; ring
  have hlt : 1 / (4 * N) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
    linarith
  have h1 : ∑ α, ∑ i, θ α i ^ 2 = 1 := hθ.2
  linarith

theorem lemmaA4 (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, ∀ z ∈ mixedProfiles n, ∀ θ ∈ unitTangent n,
      c ≤ ∫ ω, max (∑ α, (sfpChoice u z (ε t) ω α - pbr f u z α) ⬝ᵥ θ α) 0 ∂P := by
  classical
  set B : Fin p → ℝ := fun α => ∑ s' : Profile n, |u α s'| with hB
  have hne : ∀ α, (Finset.univ : Finset (Fin (n α))).Nonempty := fun α =>
    ⟨⟨0, hn α⟩, Finset.mem_univ _⟩
  set mα : Fin p → ℝ := fun α => (Finset.univ : Finset (Fin (n α))).inf' (hne α)
    (fun i => (μf (f α) (Obig (B α) i)).toReal) with hmα
  have hqpos : ∀ α (i : Fin (n α)), 0 < (μf (f α) (Obig (B α) i)).toReal := by
    intro α i
    have := isProb (hf α)
    exact ENNReal.toReal_pos (mu_pos (hf α) (isOpen_Obig _ _) (Obig_nonempty _ _)).ne'
      (measure_ne_top _ _)
  have hmpos : ∀ α, 0 < mα α := fun α => (Finset.lt_inf'_iff _).mpr fun i _ => hqpos α i
  set qmin : ℝ := ∏ α, mα α with hqmin
  have hqminp : 0 < qmin := Finset.prod_pos fun α _ => hmpos α
  have hN : 0 < ∑ α, n α := by
    have h0 : n ⟨0, by omega⟩ ≤ ∑ α, n α :=
      Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have := hn ⟨0, by omega⟩
    omega
  set c1 : ℝ := 1 / (4 * ((∑ α, n α : ℕ) : ℝ)) with hc1
  have hc1p : 0 < c1 := by
    rw [hc1]
    have : (0 : ℝ) < ((∑ α, n α : ℕ) : ℝ) := by exact_mod_cast hN
    positivity
  refine ⟨qmin * c1, mul_pos hqminp hc1p, fun t z hz θ hθ => ?_⟩
  set Y : Ω → ℝ := fun ω => ∑ α, (sfpChoice u z (ε t) ω α - pbr f u z α) ⬝ᵥ θ α with hY
  have hθb : ∀ α k, |θ α k| ≤ 1 := by
    intro α k
    have h1 : θ α k ^ 2 ≤ ∑ i, θ α i ^ 2 :=
      Finset.single_le_sum (f := fun i => θ α i ^ 2) (fun i _ => sq_nonneg (θ α i)) (Finset.mem_univ k)
    have h2 : ∑ i, θ α i ^ 2 ≤ ∑ β, ∑ i, θ β i ^ 2 :=
      Finset.single_le_sum (f := fun β => ∑ i, θ β i ^ 2)
        (fun β _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ α)
    have h3 : ∑ β, ∑ i, θ β i ^ 2 = 1 := hθ.2
    have h4 : θ α k ^ 2 ≤ 1 := by linarith
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hYexp : ∀ ω, Y ω = ∑ α, ∑ k, (sfpChoice u z (ε t) ω α k - pbr f u z α k) * θ α k := by
    intro ω; simp only [hY, dotProduct, Pi.sub_apply]
  have hpbr : ∀ α k, |pbr f u z α k| ≤ 1 := by
    intro α k
    have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
    show |choiceProb (f α) (payoffVec u z α) k| ≤ 1
    rw [abs_of_nonneg (choiceProb_nonneg _ _)]
    exact choiceProb_le_one (hf α) _ _
  have hint : ∀ α k, Integrable
      (fun ω => (sfpChoice u z (ε t) ω α k - pbr f u z α k) * θ α k) P := by
    intro α k
    refine Integrable.of_bound (((measurable_choice hε u z t α k).sub measurable_const).mul
      measurable_const).aestronglyMeasurable 2 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_choice_le u z (ε t) ω α k
    have h2 := hpbr α k
    have h3 := hθb α k
    have h4 : |sfpChoice u z (ε t) ω α k - pbr f u z α k| ≤ 2 := (abs_sub _ _).trans (by linarith)
    nlinarith [abs_nonneg (sfpChoice u z (ε t) ω α k - pbr f u z α k), abs_nonneg (θ α k)]
  have hYi : Integrable Y P := by
    have : Y = fun ω => ∑ α, ∑ k, (sfpChoice u z (ε t) ω α k - pbr f u z α k) * θ α k :=
      funext hYexp
    rw [this]
    exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun k _ => hint α k
  have hY0 : ∫ ω, Y ω ∂P = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hYexp),
      integral_finset_sum _ (fun α _ => integrable_finsetSum _ fun k _ => hint α k)]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [integral_finset_sum _ (fun k _ => hint α k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hci : Integrable (fun ω => sfpChoice u z (ε t) ω α k) P :=
      Integrable.of_bound (measurable_choice hε u z t α k).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_choice_le u z (ε t) ω α k)
    rw [integral_mul_const, integral_sub hci (integrable_const _), integral_choice hf hn hε u z t α k,
      integral_const]
    simp
  have hsplit : ∀ ω, max (Y ω) 0 - max (-Y ω) 0 = Y ω := by
    intro ω
    rcases le_total 0 (Y ω) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hpm : ∫ ω, max (Y ω) 0 ∂P = ∫ ω, max (-Y ω) 0 ∂P := by
    have := integral_sub hYi.pos_part hYi.neg_part
    rw [integral_congr_ae (Eventually.of_forall hsplit), hY0] at this
    linarith
  obtain ⟨s, hs⟩ := exists_profile_large hn hθ (fun α => pbr f u z α ⬝ᵥ θ α) hN
  set y : ℝ := ∑ α, (θ α (s α) - pbr f u z α ⬝ᵥ θ α) with hy
  set A : Set Ω := {ω | ∀ α, ε t α ω ∈ Obig (B α) (s α)} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ α, (ε t α) ⁻¹' Obig (B α) (s α) := by
      ext ω; simp only [hA, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact MeasurableSet.iInter fun α => (hε.1 t α) (isOpen_Obig _ _).measurableSet
  have hYA : ∀ ω ∈ A, Y ω = y := by
    intro ω hω
    simp only [hY, hy]
    rw [sfpChoice_eq_pureVec u hz (ε t) s hω]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [pureVec, sub_dotProduct, single_dotProduct, one_mul]
  set qs : ℝ := ∏ α, (μf (f α) (Obig (B α) (s α))).toReal with hqs
  have hPA : P.real A = qs := by
    rw [measureReal_def, hA, prob_event hε t (fun α => Obig (B α) (s α))
      (fun α => (isOpen_Obig _ _).measurableSet), ENNReal.toReal_prod]
  have hqs_ge : qmin ≤ qs :=
    Finset.prod_le_prod (fun α _ => (hmpos α).le) (fun α _ => Finset.inf'_le _ (Finset.mem_univ _))
  have hqs0 : 0 ≤ qs := hqminp.le.trans hqs_ge
  have hlow : ∀ (g : Ω → ℝ), Integrable g P → (∀ ω, 0 ≤ g ω) → ∀ c : ℝ, (∀ ω ∈ A, g ω = c) →
      qs * c ≤ ∫ ω, g ω ∂P := by
    intro g hg hg0 c hc
    have h := integral_mono ((integrable_const c).indicator hAm) hg (fun ω => by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, hc ω hω]
      · rw [Set.indicator_of_notMem hω]; exact hg0 ω)
    rw [integral_indicator_const _ hAm, smul_eq_mul, hPA] at h
    exact h
  have hpos : qs * max y 0 ≤ ∫ ω, max (Y ω) 0 ∂P :=
    hlow _ hYi.pos_part (fun ω => le_max_right _ _) _ (fun ω hω => by rw [hYA ω hω])
  have hneg : qs * max (-y) 0 ≤ ∫ ω, max (-Y ω) 0 ∂P :=
    hlow _ hYi.neg_part (fun ω => le_max_right _ _) _ (fun ω hω => by rw [hYA ω hω])
  have habs : qs * |y| ≤ ∫ ω, max (Y ω) 0 ∂P := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]; rw [max_eq_left h] at hpos; exact hpos
    · rw [abs_of_nonpos h, hpm]; rw [max_eq_left (by linarith)] at hneg; exact hneg
  have hs' : c1 ≤ |y| := hs
  calc qmin * c1 ≤ qs * |y| := mul_le_mul hqs_ge hs' hc1p.le hqs0
    _ ≤ _ := habs

end StochFictPlay.Potential.K2d

open StochFictPlay.Potential MeasureTheory ProbabilityTheory ENNReal in
theorem solution (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, ∀ z ∈ mixedProfiles n, ∀ θ ∈ unitTangent n,
      c ≤ ∫ ω, max (∑ α, (sfpChoice u z (ε t) ω α - pbr f u z α) ⬝ᵥ θ α) 0 ∂P := by
  exact StochFictPlay.Potential.K2d.lemmaA4 p hp n hn u f hf Ω P ε hε
