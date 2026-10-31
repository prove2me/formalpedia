-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.fenchel_moreau_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:44:11.870654+00:00
-- url     : https://prove2.me/submissions/0e5ea6ee-1975-4073-977c-85a80869b616

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod
import Theorems.Thm_RiskFunctionals_Polyhedral_conjugate_eq

noncomputable section
open scoped BigOperators Matrix Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open MeasureTheory Filter

namespace L1R

variable {Ω : Type*}

/-- The indicator `1_A`. -/
def ind (A : Set Ω) : Ω → ℝ := A.indicator 1

lemma ind_union {A B : Set Ω} (h : Disjoint A B) : ind (A ∪ B) = ind A + ind B := by
  funext ω
  simp only [ind, Pi.add_apply]
  rw [Set.indicator_union_of_disjoint h]

/-- Standing hypotheses: `Λ` is linear on `𝒞 = {f : G-measurable, f ∈ L_p}` and
`|Λ f| ≤ K ‖f‖₁`. -/
structure Hyp {m0 : MeasurableSpace Ω} (P : Measure[m0] Ω) (G : MeasurableSpace Ω)
    (p : ENNReal) (Λ : (Ω → ℝ) → ℝ) (K : ℝ) : Prop where
  hG : G ≤ m0
  hK : 0 ≤ K
  add : ∀ f g, Measurable[G] f → MemLp f p P → Measurable[G] g → MemLp g p P →
    Λ (f + g) = Λ f + Λ g
  smul : ∀ (c : ℝ) f, Measurable[G] f → MemLp f p P → Λ (c • f) = c * Λ f
  bd : ∀ f, Measurable[G] f → MemLp f p P → |Λ f| ≤ K * ∫ ω, |f ω| ∂P

open Classical in
/-- A signed measure from a σ-additive set function. -/
def mkSM [MeasurableSpace Ω] (ν : Set Ω → ℝ) (h0 : ν ∅ = 0)
    (hU : ∀ A : ℕ → Set Ω, (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
      HasSum (fun i => ν (A i)) (ν (⋃ i, A i))) : SignedMeasure Ω where
  measureOf' A := if MeasurableSet A then ν A else 0
  empty' := by simp [h0]
  not_measurable' A hA := if_neg hA
  m_iUnion' A hA hd := by
    have hU' : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
    simp only [hA, hU', if_true]
    exact hU A hA hd

lemma mkSM_apply [MeasurableSpace Ω] (ν : Set Ω → ℝ) (h0 : ν ∅ = 0)
    (hU : ∀ A : ℕ → Set Ω, (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
      HasSum (fun i => ν (A i)) (ν (⋃ i, A i))) {A : Set Ω} (hA : MeasurableSet A) :
    mkSM ν h0 hU A = ν A := by
  classical
  change (if MeasurableSet A then ν A else 0) = ν A
  rw [if_pos hA]

lemma sf_meas [MeasurableSpace Ω] (g : SimpleFunc Ω ℝ) : Measurable g := g.measurable
lemma sf_bdd [MeasurableSpace Ω] (g : SimpleFunc Ω ℝ) : ∃ C, ∀ x, ‖g x‖ ≤ C :=
  g.exists_forall_norm_le
lemma sf_add [MeasurableSpace Ω] (f g : SimpleFunc Ω ℝ) : ⇑(f + g) = ⇑f + ⇑g :=
  SimpleFunc.coe_add f g

variable {G : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section
variable {P : Measure Ω} [IsProbabilityMeasure P] {p : ENNReal}
  {Λ : (Ω → ℝ) → ℝ} {K : ℝ}

lemma ind_meas {A : Set Ω} (hA : MeasurableSet[G] A) : Measurable[G] (ind A) :=
  measurable_const.indicator hA

lemma ind_memLp (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    MemLp (ind A) p P :=
  memLp_indicator_const p (H.hG _ hA) 1 (Or.inr (measure_ne_top _ _))

lemma int_abs_ind (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    ∫ ω, |ind A ω| ∂P = P.real A := by
  have : (fun ω => |ind A ω|) = A.indicator 1 := by
    funext ω
    by_cases h : ω ∈ A <;> simp [ind, h]
  rw [this, integral_indicator_one (H.hG _ hA)]

lemma Λ_zero (H : Hyp P G p Λ K) : Λ 0 = 0 := by
  have := H.smul 0 0 measurable_const MemLp.zero
  simpa using this

lemma Λ_ind_bd (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    |Λ (ind A)| ≤ K * P.real A := by
  rw [← int_abs_ind H hA]
  exact H.bd _ (ind_meas hA) (ind_memLp H hA)

lemma Λ_union (H : Hyp P G p Λ K) {A B : Set Ω} (hA : MeasurableSet[G] A)
    (hB : MeasurableSet[G] B) (h : Disjoint A B) :
    Λ (ind (A ∪ B)) = Λ (ind A) + Λ (ind B) := by
  rw [ind_union h]
  exact H.add _ _ (ind_meas hA) (ind_memLp H hA) (ind_meas hB) (ind_memLp H hB)

lemma hasSum_ind (H : Hyp P G p Λ K) (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet[G] (A i))
    (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun i => Λ (ind (A i))) (Λ (ind (⋃ i, A i))) := by
  set B : ℕ → Set Ω := fun n => ⋃ i ∈ Finset.range n, A i with hBdef
  have hBm : ∀ n, MeasurableSet[G] (B n) := fun n =>
    Finset.measurableSet_biUnion _ fun i _ => hA i
  have hUm : MeasurableSet[G] (⋃ i, A i) := MeasurableSet.iUnion hA
  have hpart : ∀ n, ∑ i ∈ Finset.range n, Λ (ind (A i)) = Λ (ind (B n)) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, hBdef, Finset.notMem_empty,
        Set.iUnion_of_empty, Set.iUnion_empty]
      have : ind (∅ : Set Ω) = 0 := by funext ω; simp [ind]
      rw [this, Λ_zero H]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hBs : B (n + 1) = B n ∪ A n := by
        simp only [hBdef, Finset.range_add_one, Finset.set_biUnion_insert]
        exact Set.union_comm _ _
      have hdis : Disjoint (B n) (A n) := by
        simp only [hBdef]
        rw [Set.disjoint_iUnion₂_left]
        intro i hi
        exact hd (by simp at hi; omega)
      rw [hBs, Λ_union H (hBm n) (hA n) hdis]
  -- summability
  have hsP : Summable fun i => P.real (A i) := by
    simp only [measureReal_def]
    refine ENNReal.summable_toReal ?_
    rw [← measure_iUnion hd fun i => H.hG _ (hA i)]
    exact measure_ne_top _ _
  have hsum : Summable fun i => Λ (ind (A i)) := by
    refine Summable.of_norm_bounded (hsP.mul_left K) fun i => ?_
    rw [Real.norm_eq_abs]
    exact Λ_ind_bd H (hA i)
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [hpart]
  -- the tail
  set C : ℕ → Set Ω := fun n => (⋃ i, A i) \ B n with hCdef
  have hCm : ∀ n, MeasurableSet[G] (C n) := fun n => hUm.diff (hBm n)
  have hdiff : ∀ n, Λ (ind (⋃ i, A i)) - Λ (ind (B n)) = Λ (ind (C n)) := by
    intro n
    have hsub : B n ⊆ ⋃ i, A i := fun ω hω => by
      simp only [hBdef, Set.mem_iUnion] at hω ⊢
      obtain ⟨i, _, hi⟩ := hω
      exact ⟨i, hi⟩
    have : (⋃ i, A i) = B n ∪ C n := (Set.union_sdiff_cancel hsub).symm
    rw [this, Λ_union H (hBm n) (hCm n) Set.disjoint_sdiff_right]
    ring
  have hCt : Tendsto (fun n => P.real (C n)) atTop (𝓝 0) := by
    have hanti : Antitone C := by
      intro m n hmn ω hω
      simp only [hCdef, hBdef, Set.mem_sdiff, Set.mem_iUnion] at hω ⊢
      refine ⟨hω.1, fun ⟨i, hi, hiω⟩ => hω.2 ⟨i, ?_, hiω⟩⟩
      simp at hi ⊢; omega
    have hI : (⋂ n, C n) = ∅ := by
      ext ω
      simp only [hCdef, hBdef, Set.mem_iInter, Set.mem_sdiff, Set.mem_iUnion,
        Set.mem_empty_iff_false, iff_false, not_forall]
      by_cases h : ∃ i, ω ∈ A i
      · obtain ⟨i, hi⟩ := h
        exact ⟨i + 1, fun h' => h'.2 ⟨i, by simp, hi⟩⟩
      · exact ⟨0, fun h' => h h'.1⟩
    have := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (H.hG _ (hCm n)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hI, measure_empty] at this
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
    simpa [measureReal_def, Function.comp_def] using h2
  have hlim : Tendsto (fun n => Λ (ind (⋃ i, A i)) - Λ (ind (B n))) atTop (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hCt.const_mul K)
    rw [Real.norm_eq_abs]
    exact Λ_ind_bd H (hCm n)
  have := hlim.const_sub (Λ (ind (⋃ i, A i)))
  simpa using this

/-- The signed measure `A ↦ Λ(1_A)` on `(Ω, G)`. -/
def sm (H : Hyp P G p Λ K) : @VectorMeasure Ω G ℝ _ _ :=
  @mkSM Ω G (fun A => Λ (ind A)) (by
    have : ind (∅ : Set Ω) = 0 := by funext ω; simp [ind]
    simp only [this, Λ_zero H]) (fun A hA hd => hasSum_ind H A hA hd)

lemma sm_apply (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    sm H A = Λ (ind A) :=
  @mkSM_apply Ω G _ _ _ _ hA

lemma sm_ac (H : Hyp P G p Λ K) :
    VectorMeasure.AbsolutelyContinuous (sm H) (P.trim H.hG).toENNRealVectorMeasure := by
  intro A hA0
  by_cases hm : MeasurableSet[G] A
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hm, trim_measurableSet_eq H.hG hm]
      at hA0
    rw [sm_apply H hm]
    have := Λ_ind_bd H hm
    rw [measureReal_def, hA0] at this
    simpa using this
  · exact (sm H).not_measurable hm

/-- The Radon–Nikodym density of `A ↦ Λ(1_A)` with respect to `P` on `G`. -/
def dens (H : Hyp P G p Λ K) : Ω → ℝ := @SignedMeasure.rnDeriv Ω G (sm H) (P.trim H.hG)

lemma dens_meas (H : Hyp P G p Λ K) : Measurable[G] (dens H) := by
  unfold dens; exact SignedMeasure.measurable_rnDeriv _ _

lemma dens_int (H : Hyp P G p Λ K) : Integrable (dens H) (P.trim H.hG) := by
  unfold dens; exact SignedMeasure.integrable_rnDeriv _ _

lemma setInt_dens (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    ∫ ω in A, dens H ω ∂(P.trim H.hG) = Λ (ind A) := by
  rw [← withDensityᵥ_apply (dens_int H) hA, dens,
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (sm_ac H), sm_apply H hA]

lemma dens_le (H : Hyp P G p Λ K) : ∀ᵐ ω ∂(P.trim H.hG), dens H ω ≤ K := by
  refine ae_le_of_forall_setIntegral_le (dens_int H)
    (integrable_const K) fun A hA _ => ?_
  rw [setInt_dens H hA, setIntegral_const, smul_eq_mul, measureReal_def,
    trim_measurableSet_eq H.hG hA, ← measureReal_def, mul_comm]
  exact (le_abs_self _).trans (Λ_ind_bd H hA)

lemma le_dens (H : Hyp P G p Λ K) : ∀ᵐ ω ∂(P.trim H.hG), -K ≤ dens H ω := by
  refine ae_le_of_forall_setIntegral_le (integrable_const (-K))
    (dens_int H) fun A hA _ => ?_
  rw [setInt_dens H hA, setIntegral_const, smul_eq_mul, measureReal_def,
    trim_measurableSet_eq H.hG hA, ← measureReal_def]
  have := neg_abs_le (Λ (ind A))
  have h2 := Λ_ind_bd H hA
  nlinarith

/-- The clipped density `Z = max(-K, min(K, dens))`. -/
def Zd (H : Hyp P G p Λ K) : Ω → ℝ := fun ω => max (-K) (min K (dens H ω))

lemma Zd_meas (H : Hyp P G p Λ K) : Measurable[G] (Zd H) :=
  measurable_const.max (measurable_const.min (dens_meas H))

lemma Zd_bd (H : Hyp P G p Λ K) (ω : Ω) : |Zd H ω| ≤ K := by
  have hK := H.hK
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma Zd_ae (H : Hyp P G p Λ K) : Zd H =ᵐ[P.trim H.hG] dens H := by
  filter_upwards [dens_le H, le_dens H] with ω h1 h2
  simp only [Zd]
  rw [min_eq_right h1, max_eq_right h2]

lemma int_ind_Zd (H : Hyp P G p Λ K) {A : Set Ω} (hA : MeasurableSet[G] A) :
    ∫ ω, ind A ω * Zd H ω ∂P = Λ (ind A) := by
  have hsm : StronglyMeasurable[G] (fun ω => ind A ω * Zd H ω) :=
    ((ind_meas hA).mul (Zd_meas H)).stronglyMeasurable
  rw [integral_trim H.hG hsm]
  have : (fun ω => ind A ω * Zd H ω) = A.indicator (Zd H) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [ind, h]
  rw [this, integral_indicator hA, integral_congr_ae (ae_restrict_of_ae (Zd_ae H)),
    setInt_dens H hA]

lemma int_abs_le {p : ENNReal} (hp : 1 ≤ p) {f : Ω → ℝ} (hf : MemLp f p P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlt : eLpNorm f p P < ENNReal.ofReal δ) : ∫ ω, |f ω| ∂P ≤ δ := by
  have h1 : eLpNorm f 1 P ≤ eLpNorm f p P := eLpNorm_le_eLpNorm_of_exponent_le hp hf.1
  have h2 := (lt_of_le_of_lt h1 hlt).le
  have e : ∫ ω, |f ω| ∂P = (eLpNorm f 1 P).toReal := by
    rw [show (fun ω => |f ω|) = fun ω => ‖f ω‖ from funext fun ω => (Real.norm_eq_abs _).symm,
      integral_norm_eq_lintegral_enorm hf.1, ← eLpNorm_one_eq_lintegral_enorm]
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal hδ h2

lemma Zd_int (H : Hyp P G p Λ K) (hp : 1 ≤ p) {f : Ω → ℝ} (hf : MemLp f p P) :
    Integrable (fun ω => f ω * Zd H ω) P :=
  (hf.integrable hp).mul_bdd ((Zd_meas H).mono H.hG le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact Zd_bd H ω)

lemma rep (H : Hyp P G p Λ K) (hp : 1 ≤ p) :
    ∀ f, Measurable[G] f → MemLp f p P → Λ f = ∫ ω, f ω * Zd H ω ∂P := by
  set L : (Ω → ℝ) → ℝ := fun f => Λ f - ∫ ω, f ω * Zd H ω ∂P with hL
  have Ladd : ∀ f g, Measurable[G] f → MemLp f p P → Measurable[G] g → MemLp g p P →
      L (f + g) = L f + L g := by
    intro f g hf hf' hg hg'
    simp only [hL, H.add f g hf hf' hg hg', Pi.add_apply, add_mul]
    rw [integral_add (Zd_int H hp hf') (Zd_int H hp hg')]
    ring
  have Lsmul : ∀ (c : ℝ) f, Measurable[G] f → MemLp f p P → L (c • f) = c * L f := by
    intro c f hf hf'
    simp only [hL, H.smul c f hf hf', Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    ring
  have Lbd : ∀ f, Measurable[G] f → MemLp f p P → |L f| ≤ 2 * K * ∫ ω, |f ω| ∂P := by
    intro f hf hf'
    have h1 := H.bd f hf hf'
    have h2 : |∫ ω, f ω * Zd H ω ∂P| ≤ ∫ ω, |f ω| * K ∂P := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hf'.integrable hp).abs.mul_const K)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (Zd_bd H ω) (abs_nonneg _)
    rw [integral_mul_const] at h2
    simp only [hL]
    calc |Λ f - ∫ ω, f ω * Zd H ω ∂P| ≤ |Λ f| + |∫ ω, f ω * Zd H ω ∂P| := abs_sub _ _
      _ ≤ K * ∫ ω, |f ω| ∂P + (∫ ω, |f ω| ∂P) * K := add_le_add h1 h2
      _ = 2 * K * ∫ ω, |f ω| ∂P := by ring
  -- simple functions
  have hsimp_mem : ∀ g : @SimpleFunc Ω G ℝ, Measurable[G] g ∧ MemLp g p P := by
    intro g
    refine ⟨@sf_meas Ω G g, ?_⟩
    obtain ⟨C, hC⟩ := @sf_bdd Ω G g
    exact MemLp.of_bound ((@sf_meas Ω G g).mono H.hG le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hsimp : ∀ g : @SimpleFunc Ω G ℝ, L g = 0 := by
    intro g
    refine @SimpleFunc.induction Ω ℝ G _ (fun g => L g = 0) ?_ ?_ g
    · intro c A hA
      have e : ⇑(@SimpleFunc.piecewise Ω ℝ G A hA (@SimpleFunc.const Ω ℝ G c)
          (@SimpleFunc.const Ω ℝ G 0)) = c • ind A := by
        funext ω
        by_cases h : ω ∈ A <;> simp [SimpleFunc.coe_piecewise, Set.piecewise, h, ind]
      show L _ = 0
      rw [e, Lsmul c _ (ind_meas hA) (ind_memLp H hA)]
      simp only [hL, int_ind_Zd H hA, sub_self, mul_zero]
    · intro f g _ hf hg
      show L _ = 0
      rw [@sf_add Ω G, Ladd _ _ (hsimp_mem f).1 (hsimp_mem f).2 (hsimp_mem g).1
        (hsimp_mem g).2, hf, hg, add_zero]
  -- approximation
  intro f hf hf'
  suffices L f = 0 by simp only [hL] at this; linarith
  have hfi : Integrable f (P.trim H.hG) :=
    (hf'.integrable hp).trim H.hG hf.stronglyMeasurable
  have hK := H.hK
  refine abs_nonpos_iff.mp (le_of_forall_pos_le_add fun η hη => ?_)
  have hη' : 0 < η / (2 * K + 1) := div_pos hη (by linarith)
  obtain ⟨g, hg, -⟩ : ∃ g : @SimpleFunc Ω G ℝ,
      eLpNorm (f - ⇑g) 1 (P.trim H.hG) < ENNReal.ofReal (η / (2 * K + 1)) ∧
        MemLp g 1 (P.trim H.hG) := by
    let _ := G
    exact (memLp_one_iff_integrable.2 hfi).exists_simpleFunc_eLpNorm_sub_lt
      ENNReal.one_ne_top (by simpa using hη')
  have hfgm : Measurable[G] (f - ⇑g) := hf.sub (hsimp_mem g).1
  have hfgl : MemLp (f - ⇑g) p P := hf'.sub (hsimp_mem g).2
  rw [eLpNorm_trim H.hG hfgm.stronglyMeasurable] at hg
  have hI := int_abs_le le_rfl (hfgl.mono_exponent hp) hη'.le hg
  have hdec : L f = L (f - ⇑g) + L g := by
    rw [← Ladd _ _ hfgm hfgl (hsimp_mem g).1 (hsimp_mem g).2, sub_add_cancel]
  rw [hdec, hsimp g, add_zero, zero_add]
  have := Lbd _ hfgm hfgl
  have h3 : 2 * K * ∫ ω, |(f - ⇑g) ω| ∂P ≤ 2 * K * (η / (2 * K + 1)) :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have h4 : 2 * K * (η / (2 * K + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- Representation of an `L¹`-bounded linear functional on `L_p(G)` by a bounded density. -/
theorem exists_rep (H : Hyp P G p Λ K) (hp : 1 ≤ p) :
    ∃ Z : Ω → ℝ, Measurable[G] Z ∧ (∀ ω, |Z ω| ≤ K) ∧
      ∀ f, Measurable[G] f → MemLp f p P → Λ f = ∫ ω, f ω * Z ω ∂P :=
  ⟨Zd H, Zd_meas H, Zd_bd H, rep H hp⟩

end

end L1R

open RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace PDR

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma cone_zero {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) :
    (0 : Fin k → ℝ) ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j; simp

lemma cone_smul {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) {r : ℝ} (hr : 0 ≤ r)
    {e : Fin k → ℝ} (he : e ∈ V) : r • e ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j
  rw [dotProduct_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hr (he j)

lemma cone_add {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V)
    {x y : Fin k → ℝ} (hx : x ∈ V) (hy : y ∈ V) : x + y ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j
  rw [dotProduct_add]
  exact add_nonpos (hx j) (hy j)

lemma dot_memLp {P : Measure Ω} {p : ENNReal} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : MemLp f p P)
    (w : Fin k → ℝ) : MemLp (fun ω => w ⬝ᵥ f ω) p P := by
  have : (fun ω => w ⬝ᵥ f ω) = fun ω => ∑ i, w i * f ω i := by
    funext ω; simp [dotProduct]
  rw [this]
  exact memLp_finsetSum _ fun i _ => (hf.eval i).const_mul (w i)

lemma dot_meas {m : MeasurableSpace Ω} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : Measurable[m] f)
    (w : Fin k → ℝ) : Measurable[m] (fun ω => w ⬝ᵥ f ω) := by
  have hc : Continuous fun x : Fin k → ℝ => w ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  exact hc.measurable.comp hf

lemma abs_dot_le {k : ℕ} (w v : Fin k → ℝ) {B : ℝ} (hB : ∀ i, |v i| ≤ B) :
    |w ⬝ᵥ v| ≤ (∑ i, |w i|) * B := by
  unfold dotProduct
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)

/-! ### Linear structure of the feasible set -/

lemma feas_zero (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (hi : D.CompleteRecourse T) :
    D.Feasible P p T 𝓕 0 0 := by
  refine ⟨fun t ht => ⟨measurable_const, MemLp.zero, Filter.Eventually.of_forall fun ω =>
    cone_zero (hi.1 t ht)⟩, fun t ht => Filter.Eventually.of_forall fun ω => by simp⟩

lemma feas_comb (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (hi : D.CompleteRecourse T) {Y Y' : ℕ → Ω → ℝ}
    {v v' : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (hv' : D.Feasible P p T 𝓕 Y' v') {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    D.Feasible P p T 𝓕 (a • Y + b • Y') (a • v + b • v') := by
  refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, fun t ht => ?_⟩
  · have h1 := (hv.1 t ht).1
    have h2 := (hv'.1 t ht).1
    show Measurable[𝓕 t] (fun ω => a • v t ω + b • v' t ω)
    fun_prop
  · exact ((hv.1 t ht).2.1.const_smul a).add ((hv'.1 t ht).2.1.const_smul b)
  · filter_upwards [(hv.1 t ht).2.2, (hv'.1 t ht).2.2] with ω h1 h2
    exact cone_add (hi.1 t ht) (cone_smul (hi.1 t ht) ha h1) (cone_smul (hi.1 t ht) hb h2)
  · filter_upwards [hv.2 t ht, hv'.2 t ht] with ω h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]

lemma obj_comb (D : MultiPeriodData) {P : Measure Ω} [IsFiniteMeasure P] {p : ENNReal}
    (hp : 1 ≤ p) {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω} {Y Y' : ℕ → Ω → ℝ}
    {v v' : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (hv' : D.Feasible P p T 𝓕 Y' v') (a b : ℝ) :
    D.objective P T (a • v + b • v') = a * D.objective P T v + b * D.objective P T v' := by
  unfold objective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ T := by simp at hs; omega
  have i1 := (dot_memLp (hv.1 s hs').2.1 (D.c s)).integrable hp
  have i2 := (dot_memLp (hv'.1 s hs').2.1 (D.c s)).integrable hp
  simp only [Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul, integral_const_mul]

/-! ### Real-valued version of the sup -/

lemma le_F (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} {v : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (htop : D.functional P p T 𝓕 Y ≠ ⊤) :
    D.objective P T v ≤ (D.functional P p T 𝓕 Y).toReal := by
  have h : ((D.objective P T v : ℝ) : EReal) ≤ D.functional P p T 𝓕 Y :=
    le_sSup ⟨v, hv, rfl⟩
  have := EReal.toReal_le_toReal h (EReal.coe_ne_bot _) htop
  simpa using this

lemma F_le (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} (hbot : D.functional P p T 𝓕 Y ≠ ⊥)
    {c : ℝ} (h : ∀ v, D.Feasible P p T 𝓕 Y v → D.objective P T v ≤ c) :
    (D.functional P p T 𝓕 Y).toReal ≤ c := by
  have h1 : D.functional P p T 𝓕 Y ≤ (c : EReal) := by
    refine sSup_le ?_
    rintro x ⟨v, hv, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (h v hv)
  have := EReal.toReal_le_toReal h1 hbot (EReal.coe_ne_top _)
  simpa using this

lemma scale_le {F : ℝ} {S : ℝ → Prop} (hL2 : ∀ c, (∀ x, S x → x ≤ c) → F ≤ c)
    (hex : ∃ x, S x) {a c : ℝ} (ha : 0 ≤ a) (h : ∀ x, S x → a * x ≤ c) : a * F ≤ c := by
  rcases ha.eq_or_lt with rfl | ha
  · obtain ⟨x, hx⟩ := hex
    simpa using h x hx
  · have : F ≤ c / a := hL2 _ fun x hx => by
      rw [le_div_iff₀ ha, mul_comm]; exact h x hx
    rw [le_div_iff₀ ha, mul_comm] at this
    exact this

/-! ### Explicit feasible solution (complete recourse) -/

/-- The recursively defined feasible decision process. -/
def vv (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ) :
    (t : ℕ) → Ω → Fin (D.k t) → ℝ
  | t => fun ω =>
    let x := Y t ω - ∑ s ∈ (Finset.range t).attach, D.W t s.1 ⬝ᵥ vv D ep em Y s.1 ω
    ((|x| + x) / 2) • ep t + ((|x| - x) / 2) • em t
termination_by t => t
decreasing_by exact Finset.mem_range.mp s.2

def xval (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  Y t ω - ∑ s ∈ Finset.range t, D.W t s ⬝ᵥ vv D ep em Y s ω

lemma vv_eq (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    vv D ep em Y t ω = ((|xval D ep em Y t ω| + xval D ep em Y t ω) / 2) • ep t +
      ((|xval D ep em Y t ω| - xval D ep em Y t ω) / 2) • em t := by
  rw [vv]
  simp only [xval]
  rw [Finset.sum_attach (Finset.range t) (fun s => D.W t s ⬝ᵥ vv D ep em Y s ω)]


structure GoodE (D : MultiPeriodData) (T : ℕ) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) : Prop where
  zero_p : ep 0 = 0
  zero_m : em 0 = 0
  mem_p : ∀ t ∈ Finset.Icc 1 T, ep t ∈ D.V t
  mem_m : ∀ t ∈ Finset.Icc 1 T, em t ∈ D.V t
  dot_p : ∀ t ∈ Finset.Icc 1 T, D.W t t ⬝ᵥ ep t = 1
  dot_m : ∀ t ∈ Finset.Icc 1 T, D.W t t ⬝ᵥ em t = -1

lemma exists_goodE (D : MultiPeriodData) {T : ℕ} (hi : D.CompleteRecourse T) :
    ∃ ep em, GoodE D T ep em := by
  have h : ∀ t, ∃ e : (Fin (D.k t) → ℝ) × (Fin (D.k t) → ℝ),
      (t = 0 → e.1 = 0 ∧ e.2 = 0) ∧ (t ∈ Finset.Icc 1 T → e.1 ∈ D.V t ∧ e.2 ∈ D.V t ∧
        D.W t t ⬝ᵥ e.1 = 1 ∧ D.W t t ⬝ᵥ e.2 = -1) := by
    intro t
    by_cases ht : t ∈ Finset.Icc 1 T
    · have hs := hi.2 t ht
      have h1 : (1 : ℝ) ∈ (fun v => D.W t t ⬝ᵥ v) '' D.V t := hs ▸ Set.mem_univ _
      have h2 : (-1 : ℝ) ∈ (fun v => D.W t t ⬝ᵥ v) '' D.V t := hs ▸ Set.mem_univ _
      obtain ⟨a, ha, ha'⟩ := h1
      obtain ⟨b, hb, hb'⟩ := h2
      refine ⟨(a, b), fun h0 => ?_, fun _ => ⟨ha, hb, ha', hb'⟩⟩
      simp [h0] at ht
    · exact ⟨(0, 0), fun _ => ⟨rfl, rfl⟩, fun h => absurd h ht⟩
  choose e he using h
  exact ⟨fun t => (e t).1, fun t => (e t).2, ⟨((he 0).1 rfl).1, ((he 0).1 rfl).2,
    fun t ht => ((he t).2 ht).1, fun t ht => ((he t).2 ht).2.1,
    fun t ht => ((he t).2 ht).2.2.1, fun t ht => ((he t).2 ht).2.2.2⟩⟩

section
variable {D : MultiPeriodData} {T : ℕ} {ep em : (t : ℕ) → Fin (D.k t) → ℝ}

lemma vv_zero (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) (ω : Ω) : vv D ep em Y 0 ω = 0 := by
  rw [vv_eq, hE.zero_p, hE.zero_m]; simp

lemma vv_dot (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T)
    (ω : Ω) : D.W t t ⬝ᵥ vv D ep em Y t ω = xval D ep em Y t ω := by
  rw [vv_eq, dotProduct_add, dotProduct_smul, dotProduct_smul, hE.dot_p t ht, hE.dot_m t ht]
  simp only [smul_eq_mul]; ring

lemma vv_constr (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T)
    (ω : Ω) : ∑ s ∈ Finset.range (t + 1), D.W t s ⬝ᵥ vv D ep em Y s ω = Y t ω := by
  rw [Finset.sum_range_succ, vv_dot hE Y ht, xval]; ring

lemma vv_mem (hE : GoodE D T ep em) (hi : D.CompleteRecourse T) (Y : ℕ → Ω → ℝ) {t : ℕ}
    (ht : t ≤ T) (ω : Ω) : vv D ep em Y t ω ∈ D.V t := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [vv_zero hE]; exact cone_zero (hi.1 0 ht)
  · have ht' : t ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hpos, ht⟩
    rw [vv_eq]
    set x := xval D ep em Y t ω
    have h1 : 0 ≤ (|x| + x) / 2 := by have := neg_abs_le x; linarith
    have h2 : 0 ≤ (|x| - x) / 2 := by have := le_abs_self x; linarith
    exact cone_add (hi.1 t ht) (cone_smul (hi.1 t ht) h1 (hE.mem_p t ht'))
      (cone_smul (hi.1 t ht) h2 (hE.mem_m t ht'))

lemma vv_meas (hE : GoodE D T ep em) {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : IsFiltrationUpTo mΩ T 𝓕)
    {Y : ℕ → Ω → ℝ} (hY : ∀ t ∈ Finset.Icc 1 T, Measurable[𝓕 t] (Y t)) :
    ∀ t, t ≤ T → Measurable[𝓕 t] (vv D ep em Y t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · have : vv D ep em Y 0 = fun _ => 0 := funext fun ω => vv_zero hE Y ω
      rw [this]; exact measurable_const
    · have ht' : t ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hpos, ht⟩
      have hx : Measurable[𝓕 t] (xval D ep em Y t) := by
        have hs : ∀ s ∈ Finset.range t,
            Measurable[𝓕 t] (fun ω => D.W t s ⬝ᵥ vv D ep em Y s ω) := by
          intro s hs
          have hs' : s < t := Finset.mem_range.mp hs
          exact (dot_meas (IH s hs' (by omega)) _).mono (h𝓕.2.1 s t hs'.le ht) le_rfl
        exact (hY t ht').sub (Finset.measurable_fun_sum _ hs)
      have : vv D ep em Y t = fun ω =>
          ((|xval D ep em Y t ω| + xval D ep em Y t ω) / 2) • ep t +
          ((|xval D ep em Y t ω| - xval D ep em Y t ω) / 2) • em t :=
        funext fun ω => vv_eq D ep em Y t ω
      rw [this]
      fun_prop

/-- `S Y ω = Σ_{t=1}^T |Y_t(ω)|`. -/
def Ssum (T : ℕ) (Y : ℕ → Ω → ℝ) (ω : Ω) : ℝ := ∑ t ∈ Finset.Icc 1 T, |Y t ω|

lemma Ssum_nonneg (T : ℕ) (Y : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ Ssum T Y ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma vv_bound (hE : GoodE D T ep em) :
    ∃ C, 0 ≤ C ∧ ∀ (Y : ℕ → Ω → ℝ) (t : ℕ), t ≤ T → ∀ ω i,
      |vv D ep em Y t ω i| ≤ C * Ssum T Y ω := by
  suffices h : ∀ n, ∃ C, 0 ≤ C ∧ ∀ (Y : ℕ → Ω → ℝ) (t : ℕ), t ≤ n → t ≤ T → ∀ ω i,
      |vv D ep em Y t ω i| ≤ C * Ssum T Y ω by
    obtain ⟨C, hC, h⟩ := h T
    exact ⟨C, hC, fun Y t ht => h Y t ht ht⟩
  intro n
  induction n with
  | zero =>
    refine ⟨0, le_rfl, fun Y t ht _ ω i => ?_⟩
    have : t = 0 := by omega
    subst this
    rw [vv_zero hE]; simp
  | succ n IH =>
    obtain ⟨C, hC, hb⟩ := IH
    set A := ∑ s ∈ Finset.range (n + 1), ∑ i, |D.W (n + 1) s i|
    set E := ∑ i, (|ep (n + 1) i| + |em (n + 1) i|)
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => by positivity
    refine ⟨C + (1 + A * C) * E, by positivity, fun Y t ht hT ω i => ?_⟩
    have hS := Ssum_nonneg T Y ω
    rcases Nat.lt_or_ge t (n + 1) with hlt | hge
    · refine (hb Y t (by omega) hT ω i).trans ?_
      have : 0 ≤ (1 + A * C) * E * Ssum T Y ω := by positivity
      nlinarith
    · have htn : t = n + 1 := by omega
      subst htn
      have hmem : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hT⟩
      -- bound on x
      have hx : |xval D ep em Y (n + 1) ω| ≤ (1 + A * C) * Ssum T Y ω := by
        unfold xval
        have h1 : |Y (n + 1) ω| ≤ Ssum T Y ω :=
          Finset.single_le_sum (f := fun t => |Y t ω|) (fun _ _ => abs_nonneg _) hmem
        have h2 : |∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ vv D ep em Y s ω| ≤
            A * (C * Ssum T Y ω) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun s hs => ?_
          have hs' : s ≤ n := by simp at hs; omega
          exact abs_dot_le _ _ fun j => hb Y s hs' (by omega) ω j
        calc |Y (n + 1) ω - ∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ vv D ep em Y s ω|
            ≤ |Y (n + 1) ω| + |∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ
                vv D ep em Y s ω| := abs_sub _ _
          _ ≤ Ssum T Y ω + A * (C * Ssum T Y ω) := add_le_add h1 h2
          _ = (1 + A * C) * Ssum T Y ω := by ring
      rw [vv_eq]
      set x := xval D ep em Y (n + 1) ω
      have ha1 : 0 ≤ (|x| + x) / 2 := by have := neg_abs_le x; linarith
      have ha2 : (|x| + x) / 2 ≤ |x| := by have := le_abs_self x; linarith
      have hb1 : 0 ≤ (|x| - x) / 2 := by have := le_abs_self x; linarith
      have hb2 : (|x| - x) / 2 ≤ |x| := by have := neg_abs_le x; linarith
      have hEi : |ep (n + 1) i| + |em (n + 1) i| ≤ E :=
        Finset.single_le_sum (f := fun i => |ep (n + 1) i| + |em (n + 1) i|)
          (fun _ _ => by positivity) (Finset.mem_univ i)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |(|x| + x) / 2 * ep (n + 1) i + (|x| - x) / 2 * em (n + 1) i|
          ≤ |(|x| + x) / 2 * ep (n + 1) i| + |(|x| - x) / 2 * em (n + 1) i| := abs_add_le _ _
        _ = (|x| + x) / 2 * |ep (n + 1) i| + (|x| - x) / 2 * |em (n + 1) i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha1, abs_of_nonneg hb1]
        _ ≤ |x| * |ep (n + 1) i| + |x| * |em (n + 1) i| := by
            gcongr
        _ = |x| * (|ep (n + 1) i| + |em (n + 1) i|) := by ring
        _ ≤ ((1 + A * C) * Ssum T Y ω) * E := by
            gcongr
        _ ≤ (C + (1 + A * C) * E) * Ssum T Y ω := by nlinarith

lemma Ssum_memLp {P : Measure Ω} {p : ENNReal} {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ}
    (hY : IsAdaptedLp P p T 𝓕 Y) : MemLp (Ssum T Y) p P := by
  have : Ssum T Y = fun ω => ∑ t ∈ Finset.Icc 1 T, ‖Y t ω‖ := by
    funext ω; simp [Ssum, Real.norm_eq_abs]
  rw [this]
  exact memLp_finsetSum _ fun t ht => (hY t ht).2.norm

lemma vv_feas (hE : GoodE D T ep em) (hi : D.CompleteRecourse T) {P : Measure Ω}
    {p : ENNReal} {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : IsFiltrationUpTo mΩ T 𝓕)
    {Y : ℕ → Ω → ℝ} (hY : IsAdaptedLp P p T 𝓕 Y) :
    D.Feasible P p T 𝓕 Y (vv D ep em Y) := by
  obtain ⟨C, hC, hb⟩ := vv_bound (Ω := Ω) hE
  have hm := vv_meas hE h𝓕 (fun t ht => (hY t ht).1)
  refine ⟨fun t ht => ⟨hm t ht, ?_, Filter.Eventually.of_forall fun ω => vv_mem hE hi Y ht ω⟩,
    fun t ht => Filter.Eventually.of_forall fun ω => vv_constr hE Y ht ω⟩
  refine MemLp.of_le ((Ssum_memLp hY).const_mul C)
    ((hm t ht).mono (h𝓕.2.2 t ht) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ C * Ssum T Y ω := mul_nonneg hC (Ssum_nonneg T Y ω)
  rw [Real.norm_of_nonneg h0]
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact hb Y t ht ω i

lemma obj_lb (hE : GoodE D T ep em) {P : Measure Ω} [IsProbabilityMeasure P] {p : ENNReal}
    (hp : 1 ≤ p) :
    ∃ K, 0 ≤ K ∧ ∀ {𝓕 : ℕ → MeasurableSpace Ω} (Y : ℕ → Ω → ℝ),
      IsFiltrationUpTo mΩ T 𝓕 → IsAdaptedLp P p T 𝓕 Y →
      -(K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P) ≤ D.objective P T (vv D ep em Y) := by
  obtain ⟨C, hC, hb⟩ := vv_bound (Ω := Ω) hE
  set a : ℕ → ℝ := fun t => ∑ i, |D.c t i|
  have ha : ∀ t, 0 ≤ a t := fun t => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C * ∑ t ∈ Finset.range (T + 1), a t,
    mul_nonneg hC (Finset.sum_nonneg fun t _ => ha t), fun {𝓕} Y h𝓕 hY => ?_⟩
  have hSi : Integrable (Ssum T Y) P := (Ssum_memLp hY).integrable hp
  have hIS : ∫ ω, Ssum T Y ω ∂P = ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P := by
    unfold Ssum
    rw [integral_finsetSum]
    intro t ht
    exact ((hY t ht).2.integrable hp).abs
  rw [← hIS]
  unfold objective
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht' : t ≤ T := by simp at ht; omega
  have hg : Integrable (fun ω => a t * (C * Ssum T Y ω)) P := (hSi.const_mul C).const_mul _
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun ω =>
    (show ‖D.c t ⬝ᵥ vv D ep em Y t ω‖ ≤ a t * (C * Ssum T Y ω) by
      rw [Real.norm_eq_abs]
      exact abs_dot_le _ _ fun i => hb Y t ht' ω i))
  rw [integral_const_mul, integral_const_mul, Real.norm_eq_abs] at hle
  have := neg_abs_le (∫ ω, D.c t ⬝ᵥ vv D ep em Y t ω ∂P)
  have e : C * (a t * ∫ ω, Ssum T Y ω ∂P) = a t * (C * ∫ ω, Ssum T Y ω ∂P) := by ring
  rw [e]
  linarith
end

end PDR

namespace PDR

lemma int_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p : ENNReal} (hp : 1 ≤ p) {f : Ω → ℝ} (hf : MemLp f p P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlt : eLpNorm f p P < ENNReal.ofReal δ) : ∫ ω, |f ω| ∂P ≤ δ := by
  have h1 : eLpNorm f 1 P ≤ eLpNorm f p P := eLpNorm_le_eLpNorm_of_exponent_le hp hf.1
  have h2 := (lt_of_le_of_lt h1 hlt).le
  have e : ∫ ω, |f ω| ∂P = (eLpNorm f 1 P).toReal := by
    rw [show (fun ω => |f ω|) = fun ω => ‖f ω‖ from funext fun ω => (Real.norm_eq_abs _).symm,
      integral_norm_eq_lintegral_enorm hf.1, ← eLpNorm_one_eq_lintegral_enorm]
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal hδ h2

end PDR


namespace PDR

lemma functional_congr {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData) (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) {Y Y' : ℕ → Ω → ℝ}
    (h : ∀ t ∈ Finset.Icc 1 T, Y t = Y' t) :
    D.functional P p T 𝓕 Y = D.functional P p T 𝓕 Y' := by
  have hF : ∀ v, D.Feasible P p T 𝓕 Y v ↔ D.Feasible P p T 𝓕 Y' v := by
    intro v
    unfold Feasible
    refine and_congr Iff.rfl (forall₂_congr fun t ht => ?_)
    rw [h t ht]
  unfold functional
  simp_rw [hF]

lemma adapted_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} (hY : IsAdaptedLp P p T 𝓕 Y) (t : ℕ) :
    IsAdaptedLp P p T 𝓕 (Pi.single t (Y t)) := by
  intro s hs
  by_cases hst : s = t
  · subst hst; simp only [Pi.single_eq_same]; exact hY s hs
  · simp only [Pi.single_eq_of_ne hst]; exact ⟨measurable_const, MemLp.zero⟩

lemma single_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (t : ℕ) {h : Ω → ℝ} (hm : Measurable[𝓕 t] h)
    (hl : MemLp h p P) : IsAdaptedLp P p T 𝓕 (Pi.single t h) := by
  intro s hs
  by_cases hst : s = t
  · subst hst; simp only [Pi.single_eq_same]; exact ⟨hm, hl⟩
  · simp only [Pi.single_eq_of_ne hst]; exact ⟨measurable_const, MemLp.zero⟩

end PDR

open PDR in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y =
        sInf {x : EReal | ∃ Z : ℕ → Ω → ℝ, IsAdaptedLp P q T 𝓕 Z ∧
          x = (pairing P T Y Z : EReal) - D.conjugate P p T 𝓕 Z} := by
  have hce := conjugate_eq P p q hp hp_top hpq T hT 𝓕 h𝓕 D hD hi hii
  -- weak duality
  have hwd : ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ Z ∈ D.dualSet P q T 𝓕,
      D.functional P p T 𝓕 Y ≤ (pairing P T Y Z : EReal) := by
    intro Y hY Z hZ
    have h0 := (hce Z hZ.1).1 hZ
    have h1 : D.conjugate P p T 𝓕 Z ≤ (pairing P T Y Z : EReal) - D.functional P p T 𝓕 Y :=
      sInf_le ⟨Y, hY, rfl⟩
    rw [h0] at h1
    exact (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).mp h1
  -- a point of the dual set: the constant process `ū`
  obtain ⟨u, hu0, hut⟩ := id hii
  have hZbar : (fun τ (_ : Ω) => u τ) ∈ D.dualSet P q T 𝓕 := by
    refine ⟨fun t ht => ⟨measurable_const, memLp_const _⟩, ?_, fun t ht => ?_⟩
    · simpa using hu0
    · have hle : 𝓕 t ≤ mΩ := h𝓕.2.2 t (Finset.mem_Icc.mp ht).2
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only [condExp_const hle]
      exact hut t ht
  -- the explicit feasible solution
  obtain ⟨ep, em, hE⟩ := exists_goodE D hi
  have hfin : ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤ := by
    intro Y hY
    constructor
    · have h : ((D.objective P T (vv D ep em Y) : ℝ) : EReal) ≤ D.functional P p T 𝓕 Y :=
        le_sSup ⟨_, vv_feas hE hi h𝓕 hY, rfl⟩
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top (pairing P T Y (fun τ (_ : Ω) => u τ)))
        (hwd Y hY _ hZbar)
  -- real-valued sup
  set F : (ℕ → Ω → ℝ) → ℝ := fun Y => (D.functional P p T 𝓕 Y).toReal with hFdef
  have hL1 : ∀ Y v, IsAdaptedLp P p T 𝓕 Y → D.Feasible P p T 𝓕 Y v →
      D.objective P T v ≤ F Y := fun Y v hY hv => le_F D hv (hfin Y hY).2
  have hL2 : ∀ Y, IsAdaptedLp P p T 𝓕 Y → ∀ c : ℝ,
      (∀ x, (∃ v, D.Feasible P p T 𝓕 Y v ∧ D.objective P T v = x) → x ≤ c) → F Y ≤ c :=
    fun Y hY c h => F_le D (hfin Y hY).1 fun v hv => h _ ⟨v, hv, rfl⟩
  have hex : ∀ Y, IsAdaptedLp P p T 𝓕 Y →
      ∃ x, ∃ v, D.Feasible P p T 𝓕 Y v ∧ D.objective P T v = x :=
    fun Y hY => ⟨_, _, vv_feas hE hi h𝓕 hY, rfl⟩
  have hAd : ∀ Y Y', IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' → ∀ a b : ℝ,
      IsAdaptedLp P p T 𝓕 (a • Y + b • Y') := by
    intro Y Y' hY hY' a b t ht
    have h1 := (hY t ht).1
    have h2 := (hY' t ht).1
    refine ⟨?_, ((hY t ht).2.const_smul a).add ((hY' t ht).2.const_smul b)⟩
    show Measurable[𝓕 t] (fun ω => a • Y t ω + b • Y' t ω)
    fun_prop
  have hzero : IsAdaptedLp P p T 𝓕 (0 : ℕ → Ω → ℝ) := fun t ht =>
    ⟨measurable_const, MemLp.zero⟩
  have hcomb : ∀ Y Y', IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' → ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a * F Y + b * F Y' ≤ F (a • Y + b • Y') := by
    intro Y Y' hY hY' a b ha hb
    have hmix := hAd Y Y' hY hY' a b
    have key : ∀ v v', D.Feasible P p T 𝓕 Y v → D.Feasible P p T 𝓕 Y' v' →
        a * D.objective P T v + b * D.objective P T v' ≤ F (a • Y + b • Y') := by
      intro v v' hv hv'
      rw [← obj_comb D hp hv hv' a b]
      exact hL1 _ _ hmix (feas_comb D hi hv hv' ha hb)
    have step1 : ∀ v', D.Feasible P p T 𝓕 Y' v' →
        a * F Y + b * D.objective P T v' ≤ F (a • Y + b • Y') := by
      intro v' hv'
      have := scale_le (hL2 Y hY) (hex Y hY) ha
        (c := F (a • Y + b • Y') - b * D.objective P T v') (by
          rintro x ⟨v, hv, rfl⟩
          linarith [key v v' hv hv'])
      linarith
    have := scale_le (hL2 Y' hY') (hex Y' hY') hb (c := F (a • Y + b • Y') - a * F Y) (by
      rintro x ⟨v', hv', rfl⟩
      linarith [step1 v' hv'])
    linarith
  have hPH : ∀ Y, IsAdaptedLp P p T 𝓕 Y → ∀ lam : ℝ, 0 < lam → F (lam • Y) = lam * F Y := by
    intro Y hY lam hlam
    have hY' : IsAdaptedLp P p T 𝓕 (lam • Y) := by
      have := hAd Y 0 hY hzero lam 0
      rwa [zero_smul, add_zero] at this
    apply le_antisymm
    · have h := hcomb (lam • Y) 0 hY' hzero lam⁻¹ 0 (inv_nonneg.mpr hlam.le) le_rfl
      rw [zero_smul, add_zero, zero_mul, add_zero, smul_smul, inv_mul_cancel₀ hlam.ne',
        one_smul] at h
      exact (inv_mul_le_iff₀ hlam).mp h
    · have h := hcomb Y 0 hY hzero lam 0 hlam.le le_rfl
      rwa [zero_smul, add_zero, zero_mul, add_zero] at h
  have hF0 : F 0 = 0 := by
    have := hPH 0 hzero 2 two_pos
    rw [smul_zero] at this
    linarith
  obtain ⟨K, hK, hlb⟩ := obj_lb hE (P := P) hp
  have hFlb : ∀ Y, IsAdaptedLp P p T 𝓕 Y →
      -(K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P) ≤ F Y := fun Y hY =>
    (hlb Y h𝓕 hY).trans (hL1 _ _ hY (vv_feas hE hi h𝓕 hY))
  -- strong duality
  intro Y hY
  have hRY : D.functional P p T 𝓕 Y = (F Y : EReal) :=
    (EReal.coe_toReal (hfin Y hY).2 (hfin Y hY).1).symm
  apply le_antisymm
  · refine le_sInf ?_
    rintro x ⟨Z, hZq, rfl⟩
    by_cases hZ : Z ∈ D.dualSet P q T 𝓕
    · rw [(hce Z hZq).1 hZ, sub_zero]; exact hwd Y hY Z hZ
    · rw [(hce Z hZq).2 hZ, EReal.coe_sub_bot]; exact le_top
  · -- Hahn–Banach on the space `𝒴` of adapted `L_p` processes
    let S : Submodule ℝ (ℕ → Ω → ℝ) :=
      { carrier := {Y | IsAdaptedLp P p T 𝓕 Y}
        add_mem' := fun {a b} ha hb => by
          have := hAd a b ha hb 1 1
          simpa using this
        zero_mem' := hzero
        smul_mem' := fun c a ha => by
          have := hAd a 0 ha hzero c 0
          simpa using this }
    let N : S → ℝ := fun x => -F x.1
    have N_hom : ∀ c : ℝ, 0 < c → ∀ x : S, N (c • x) = c * N x := by
      intro c hc x
      simp only [N, Submodule.coe_smul]
      rw [hPH x.1 x.2 c hc]
      ring
    have N_add : ∀ x y : S, N (x + y) ≤ N x + N y := by
      intro x y
      simp only [N, Submodule.coe_add]
      have := hcomb x.1 y.1 x.2 y.2 1 1 zero_le_one zero_le_one
      simp only [one_smul, one_mul] at this
      linarith
    have hFle : ∀ c : ℝ, F (c • Y) ≤ c * F Y := by
      intro c
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · have hY' : IsAdaptedLp P p T 𝓕 (-Y) := by
          have := hAd Y 0 hY hzero (-1) 0
          simpa using this
        have e : c • Y = (-c) • (-Y) := by rw [smul_neg, neg_smul, neg_neg]
        rw [e, hPH (-Y) hY' (-c) (by linarith)]
        have := hcomb Y (-Y) hY hY' 1 1 zero_le_one zero_le_one
        simp only [one_smul, one_mul, add_neg_cancel] at this
        rw [hF0] at this
        nlinarith
      · simp [hF0]
      · rw [hPH Y hY c hc]
    set Yel : S := ⟨Y, hY⟩ with hYel
    have hH : ∀ c : ℝ, c • Yel = 0 → (RingHom.id ℝ) c • N Yel = 0 := by
      intro c hc
      by_cases h0 : c = 0
      · simp [h0]
      · have h1 : Yel = 0 := (smul_eq_zero.mp hc).resolve_left h0
        have h2 : N Yel = 0 := by
          rw [h1]
          simp only [N, Submodule.coe_zero, hF0, neg_zero]
        rw [h2, smul_zero]
    let f := LinearPMap.mkSpanSingleton' Yel (N Yel) hH
    have hf : ∀ x : f.domain, f x ≤ N x := by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [LinearPMap.mkSpanSingleton'_apply]
      simp only [RingHom.id_apply, smul_eq_mul, N, Submodule.coe_smul]
      have := hFle c
      linarith
    obtain ⟨g, hgf, hgN⟩ := exists_extension_of_le_sublinear f N N_hom N_add hf
    set φ : S → ℝ := fun x => -g x with hφdef
    have φ_add : ∀ x y : S, φ (x + y) = φ x + φ y := fun x y => by
      simp only [φ, map_add]; ring
    have φ_neg : ∀ x : S, φ (-x) = -φ x := fun x => by simp only [φ, map_neg]
    have φ_smul : ∀ (c : ℝ) (x : S), φ (c • x) = c * φ x := fun c x => by
      simp only [φ, map_smul, smul_eq_mul]; ring
    have hφF : ∀ x : S, F x.1 ≤ φ x := fun x => by
      have := hgN x
      simp only [N] at this
      simp only [φ]
      linarith
    have hφY : φ Yel = F Y := by
      have h1 : g Yel = N Yel := by
        rw [show g Yel = g ↑(⟨Yel, Submodule.mem_span_singleton_self Yel⟩ : f.domain) from rfl,
          hgf]
        exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _
      simp only [φ, N] at h1 ⊢
      rw [h1]
      simp [hYel]
    have hφbd : ∀ x : S, |φ x| ≤ K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |x.1 t ω| ∂P := by
      intro x
      have h1 := (hFlb x.1 x.2).trans (hφF x)
      have h2 := (hFlb (-x).1 (-x).2).trans (hφF (-x))
      have e2 : ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(-x).1 t ω| ∂P =
          ∑ t ∈ Finset.Icc 1 T, ∫ ω, |x.1 t ω| ∂P := by
        simp [abs_neg]
      rw [φ_neg, e2] at h2
      rw [abs_le]
      constructor <;> linarith
    -- the coordinate functionals
    classical
    let Λ : ℕ → (Ω → ℝ) → ℝ := fun t h =>
      if hh : Measurable[𝓕 t] h ∧ MemLp h p P then
        φ ⟨Pi.single t h, single_mem t hh.1 hh.2⟩ else 0
    have hHyp : ∀ t ∈ Finset.Icc 1 T, L1R.Hyp P (𝓕 t) p (Λ t) K := by
      intro t ht
      refine ⟨h𝓕.2.2 t (Finset.mem_Icc.mp ht).2, hK, ?_, ?_, ?_⟩
      · intro a b ha ha' hb hb'
        have hab : Measurable[𝓕 t] (a + b) ∧ MemLp (a + b) p P := ⟨ha.add hb, ha'.add hb'⟩
        simp only [Λ, dif_pos hab, dif_pos (And.intro ha ha'), dif_pos (And.intro hb hb')]
        rw [← φ_add]
        congr 1
        refine Subtype.ext ?_
        funext s
        by_cases hst : s = t
        · subst hst; simp
        · simp [Pi.single_eq_of_ne hst]
      · intro c a ha ha'
        have hca : Measurable[𝓕 t] (c • a) ∧ MemLp (c • a) p P :=
          ⟨ha.const_smul c, ha'.const_smul c⟩
        simp only [Λ, dif_pos hca, dif_pos (And.intro ha ha')]
        rw [← φ_smul]
        congr 1
        refine Subtype.ext ?_
        funext s
        by_cases hst : s = t
        · subst hst; simp
        · simp [Pi.single_eq_of_ne hst]
      · intro a ha ha'
        simp only [Λ, dif_pos (And.intro ha ha')]
        refine (hφbd _).trans (le_of_eq ?_)
        congr 1
        rw [Finset.sum_eq_single t]
        · simp
        · intro s _ hst; simp [Pi.single_eq_of_ne hst]
        · intro h; exact absurd ht h
    have hrep : ∀ t, ∃ Z : Ω → ℝ, t ∈ Finset.Icc 1 T → (Measurable[𝓕 t] Z ∧
        (∀ ω, |Z ω| ≤ K) ∧ ∀ h, Measurable[𝓕 t] h → MemLp h p P →
          Λ t h = ∫ ω, h ω * Z ω ∂P) := by
      intro t
      by_cases ht : t ∈ Finset.Icc 1 T
      · obtain ⟨Z, h1, h2, h3⟩ := L1R.exists_rep (hHyp t ht) hp
        exact ⟨Z, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun h => absurd h ht⟩
    choose Zs hZs using hrep
    -- `φ` is the pairing with `Zs`
    have hφpair : ∀ x : S, φ x = pairing P T x.1 Zs := by
      intro x
      let e : ℕ → S := fun t => ⟨Pi.single t (x.1 t), adapted_single x.2 t⟩
      set r : S := x - ∑ t ∈ Finset.Icc 1 T, e t with hrdef
      have hdec : x = ∑ t ∈ Finset.Icc 1 T, e t + r := by rw [hrdef]; abel
      have hr : ∀ s ∈ Finset.Icc 1 T, r.1 s = 0 := by
        intro s hs
        simp only [hrdef, Submodule.coe_sub, Submodule.coe_sum, e, Pi.sub_apply,
          Finset.sum_apply]
        rw [Finset.sum_eq_single s]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne (Ne.symm hb)]
        · intro h; exact absurd hs h
      have hφr : φ r = 0 := by
        have hFr : F r.1 = 0 := by
          have : D.functional P p T 𝓕 r.1 = D.functional P p T 𝓕 0 :=
            functional_congr D P p T 𝓕 fun t ht => by rw [hr t ht]; rfl
          simp only [F, this]
          exact hF0
        have hFr' : F (-r).1 = 0 := by
          have : D.functional P p T 𝓕 (-r).1 = D.functional P p T 𝓕 0 :=
            functional_congr D P p T 𝓕 fun t ht => by
              simp only [Submodule.coe_neg, Pi.neg_apply, hr t ht, neg_zero]; rfl
          simp only [F, this]
          exact hF0
        have h1 := hφF r
        have h2 := hφF (-r)
        rw [φ_neg] at h2
        linarith
      have hsum : ∀ (s : Finset ℕ), φ (∑ t ∈ s, e t) = ∑ t ∈ s, φ (e t) := by
        intro s
        simp only [φ, map_sum, Finset.sum_neg_distrib]
      have he : ∀ t ∈ Finset.Icc 1 T, φ (e t) = ∫ ω, x.1 t ω * Zs t ω ∂P := by
        intro t ht
        rw [← (hZs t ht).2.2 (x.1 t) (x.2 t ht).1 (x.2 t ht).2]
        simp only [Λ, dif_pos (And.intro (x.2 t ht).1 (x.2 t ht).2)]
        rfl
      calc φ x = φ (∑ t ∈ Finset.Icc 1 T, e t + r) := by rw [← hdec]
        _ = ∑ t ∈ Finset.Icc 1 T, φ (e t) := by rw [φ_add, hφr, add_zero, hsum]
        _ = pairing P T x.1 Zs := Finset.sum_congr rfl he
    have hZq : IsAdaptedLp P q T 𝓕 Zs := fun t ht =>
      ⟨(hZs t ht).1, MemLp.of_bound
        (((hZs t ht).1.mono (h𝓕.2.2 t (Finset.mem_Icc.mp ht).2) le_rfl).aestronglyMeasurable)
        K (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (hZs t ht).2.1 ω)⟩
    have hconj : 0 ≤ D.conjugate P p T 𝓕 Zs := by
      refine le_sInf ?_
      rintro x ⟨Y', hY', rfl⟩
      have h1 := hφF ⟨Y', hY'⟩
      rw [hφpair] at h1
      rw [(EReal.coe_toReal (hfin Y' hY').2 (hfin Y' hY').1).symm, ← EReal.coe_sub]
      exact EReal.coe_nonneg.mpr (by simp only [F] at h1; linarith)
    have hZd : Zs ∈ D.dualSet P q T 𝓕 := by
      by_contra hn
      rw [(hce Zs hZq).2 hn] at hconj
      exact absurd hconj (by simp)
    refine sInf_le_of_le ⟨Zs, hZq, rfl⟩ ?_
    rw [(hce Zs hZq).1 hZd, sub_zero, hRY]
    have := hφpair Yel
    rw [hφY] at this
    rw [this]
