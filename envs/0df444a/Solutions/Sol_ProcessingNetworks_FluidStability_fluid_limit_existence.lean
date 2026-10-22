-- Prove2me | solution 1 for ProcessingNetworks.FluidStability.fluid_limit_existence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:03:36.859379+00:00
-- url     : https://prove2.me/submissions/2941083d-69dd-4ee8-9213-5cdc6366d1e4

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily



namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability Topology
open scoped ENNReal

namespace FLECex

open Classical

noncomputable def μU : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1)

instance : IsProbabilityMeasure μU := ⟨by simp [μU, Real.volume_Ioo]⟩

noncomputable def μB : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure μB := by unfold μB; infer_instance

noncomputable def πN : Measure ℕ := geometricMeasure ⟨1/2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure πN := by unfold πN; infer_instance

lemma πN_singleton (n : ℕ) : πN {n} = ENNReal.ofReal ((1 - (1/2 : ℝ)) ^ n * (1/2)) := by
  unfold πN
  rw [geometricMeasure_singleton (by simp [← Subtype.coe_ne_coe])]

lemma πN_singleton_ne_zero (n : ℕ) : πN {n} ≠ 0 := by
  rw [πN_singleton]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

lemma πN_singleton_ne_top (n : ℕ) : πN {n} ≠ ⊤ := by
  rw [πN_singleton]; exact ENNReal.ofReal_ne_top

abbrev U : Type := ℕ → ℝ
abbrev Cn : Type := ℕ → Bool
abbrev Ωc : Type := U × (ℕ × Cn)

noncomputable def μC : Measure (ℕ × Cn) := πN.prod (Measure.infinitePi (fun _ : ℕ => μB))

instance : IsProbabilityMeasure μC := by unfold μC; infer_instance

noncomputable instance msΩ : MeasureSpace Ωc :=
  ⟨(Measure.infinitePi (fun _ : ℕ => μU)).prod μC⟩

lemma vol_eq : (ℙ : Measure Ωc) = (Measure.infinitePi (fun _ : ℕ => μU)).prod μC := rfl

instance : IsProbabilityMeasure (ℙ : Measure Ωc) := by
  rw [vol_eq]; infer_instance

lemma map_fst : (ℙ : Measure Ωc).map Prod.fst = Measure.infinitePi (fun _ : ℕ => μU) := by
  rw [vol_eq, Measure.map_fst_prod, measure_univ, one_smul]

lemma indep_cross : Indep (MeasurableSpace.comap (Prod.fst : Ωc → _) inferInstance)
    (MeasurableSpace.comap (Prod.snd : Ωc → _) inferInstance) ℙ := by
  have := indepFun_prod (μ := Measure.infinitePi (fun _ : ℕ => μU))
    (ν := μC) (X := id) (Y := id) measurable_id measurable_id
  rw [IndepFun_iff_Indep] at this
  exact this

/-- the "good" sequences of uniforms -/
def G : Set (ℕ → ℝ) :=
  {u | (∀ n, u n ∈ Set.Ioo (0:ℝ) 1) ∧ ∀ M : ℕ, ∃ n, (M : ℝ) ≤ ∑ k ∈ Finset.range n, -Real.log (u k)}

lemma G_meas : MeasurableSet G := by
  have h1 : MeasurableSet {u : ℕ → ℝ | ∀ n, u n ∈ Set.Ioo (0:ℝ) 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun n => measurableSet_Ioo.preimage (measurable_pi_apply n)
  have h2 : MeasurableSet {u : ℕ → ℝ | ∀ M : ℕ, ∃ n, (M : ℝ) ≤
      ∑ k ∈ Finset.range n, -Real.log (u k)} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n => ?_
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).log).neg)
  exact h1.inter h2

lemma ioo_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), ∀ n, u n ∈ Set.Ioo (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro n
  have h : (Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n) = μU :=
    Measure.infinitePi_map_eval _ n
  have : ∀ᵐ y ∂μU, y ∈ Set.Ioo (0:ℝ) 1 := by
    unfold μU; exact ae_restrict_mem measurableSet_Ioo
  rw [← h] at this
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable this

lemma bc_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)),
    ∃ᶠ n in atTop, u ∈ {u : ℕ → ℝ | u n < Real.exp (-1)} := by
  set s : ℕ → Set (ℕ → ℝ) := fun n => {u | u n < Real.exp (-1)} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_Iio.preimage (measurable_pi_apply n)
  have hind : iIndepSet s (Measure.infinitePi (fun _ : ℕ => μU)) := by
    rw [iIndepSet_iff_iIndep]
    have h0 := iIndepFun_infinitePi (P := fun _ : ℕ => μU) (X := fun _ => (id : ℝ → ℝ))
      (fun _ => measurable_id)
    rw [iIndepFun_iff_iIndep] at h0
    refine iIndep_of_iIndep_of_le h0 (fun n => ?_)
    refine MeasurableSpace.generateFrom_le ?_
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨Set.Iio (Real.exp (-1)), measurableSet_Iio, rfl⟩
  have hmeas : ∀ n, (Measure.infinitePi (fun _ : ℕ => μU)) (s n) = ENNReal.ofReal (Real.exp (-1)) := by
    intro n
    have h : (Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n) = μU :=
      Measure.infinitePi_map_eval _ n
    have : (Measure.infinitePi (fun _ : ℕ => μU)) (s n) =
        ((Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n)) (Set.Iio (Real.exp (-1))) := by
      rw [Measure.map_apply (measurable_pi_apply n) measurableSet_Iio]; rfl
    rw [this, h, μU, Measure.restrict_apply measurableSet_Iio]
    have he : Set.Iio (Real.exp (-1)) ∩ Set.Ioo 0 1 = Set.Ioo 0 (Real.exp (-1)) := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
      have : Real.exp (-1) < 1 := by
        have := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num); simpa using this
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [he, Real.volume_Ioo, sub_zero]
  have hsum : (∑' n, (Measure.infinitePi (fun _ : ℕ => μU)) (s n)) = ∞ := by
    simp only [hmeas]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero]
    simp [Real.exp_pos]
  have h1 := measure_limsup_eq_one hsm hind hsum
  have : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), u ∈ limsup s atTop := by
    rw [ae_iff]
    have : {a | a ∉ limsup s atTop} = (limsup s atTop)ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hsm)]
    exact h1
  filter_upwards [this] with u hu
  rw [Filter.mem_limsup_iff_frequently_mem] at hu
  exact hu

lemma G_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), u ∈ G := by
  filter_upwards [ioo_ae, bc_ae] with u h1 h2
  refine ⟨h1, ?_⟩
  have hpos : ∀ k, 0 < -Real.log (u k) := fun k => by
    have := h1 k
    have := Real.log_neg this.1 this.2
    linarith
  intro M
  induction M with
  | zero => exact ⟨0, by simp⟩
  | succ M ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨k, hk, hk2⟩ := (Filter.frequently_atTop.mp h2) n
    refine ⟨k + 1, ?_⟩
    have hlog : 1 < -Real.log (u k) := by
      have hk2' : u k < Real.exp (-1) := hk2
      have h0 := (h1 k).1
      have : Real.log (u k) < -1 := by
        rw [Real.log_lt_iff_lt_exp h0]; exact hk2'
      linarith
    have hmono : ∑ i ∈ Finset.range n, -Real.log (u i) ≤ ∑ i ∈ Finset.range k, -Real.log (u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun i _ _ => (hpos i).le)
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- clocks as a function of the uniform coordinates -/
noncomputable def Fcl (u : U) : ℕ → ℝ := fun n => if u ∈ G then -Real.log (u n) else 1

lemma Fcl_meas : Measurable Fcl := by
  rw [measurable_pi_iff]; intro n
  show Measurable fun u : ℕ → ℝ => if u ∈ G then -Real.log (u n) else 1
  exact Measurable.ite G_meas ((measurable_pi_apply n).log.neg) measurable_const

lemma Fcl_meas' (n : ℕ) : Measurable fun u : U => Fcl u n := (measurable_pi_apply n).comp Fcl_meas

lemma Fcl_pos (u : U) (n : ℕ) : 0 < Fcl u n := by
  unfold Fcl; split_ifs with h
  · have h1 := h.1 n; have := Real.log_neg h1.1 h1.2; linarith
  · norm_num

noncomputable def cl (n : ℕ) (ω : Ωc) : ℝ := Fcl ω.1 n

lemma cl_pos (n : ℕ) (ω : Ωc) : 0 < cl n ω := Fcl_pos _ _

/-- the jump times as a function of the uniform coordinates -/
noncomputable def σ (n : ℕ) (u : U) : ℝ := ∑ k ∈ Finset.range n, Fcl u k

lemma σ_meas (n : ℕ) : Measurable fun u : U => σ n u :=
  Finset.measurable_sum _ fun k _ => Fcl_meas' k

lemma σ_zero (u : U) : σ 0 u = 0 := by simp [σ]

lemma σ_strictMono (u : U) : StrictMono (fun n => σ n u) := by
  apply strictMono_nat_of_lt_succ; intro n
  simp only [σ, Finset.sum_range_succ]; linarith [Fcl_pos u n]

lemma σ_tendsto (u : U) : Tendsto (fun n => σ n u) atTop atTop := by
  by_cases h : u ∈ G
  · apply tendsto_atTop_atTop_of_monotone (σ_strictMono u).monotone
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge b
    obtain ⟨n, hn⟩ := h.2 M
    refine ⟨n, ?_⟩
    simp only [σ, Fcl, if_pos h]; linarith
  · have : (fun n => σ n u) = fun n : ℕ => (n : ℝ) := by
      funext n; simp [σ, Fcl, if_neg h]
    rw [this]; exact tendsto_natCast_atTop_atTop

lemma exists_σ_gt (t : ℝ) (u : U) : ∃ n, t < σ (n + 1) u := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp (σ_tendsto u)) (t + 1)
  exact ⟨N, by linarith [hN (N + 1) (by omega)]⟩

/-- the index of the current holding interval: `σ n ≤ t < σ (n+1)` -/
noncomputable def idx (t : ℝ) (u : U) : ℕ := Nat.find (exists_σ_gt t u)

lemma idx_lt (t : ℝ) (u : U) : t < σ (idx t u + 1) u := Nat.find_spec (exists_σ_gt t u)

lemma σ_one_pos (u : U) : 0 < σ 1 u := by
  have := σ_strictMono u (show 0 < 1 by norm_num); simpa [σ_zero] using this

lemma idx_eq_of (t : ℝ) (u : U) (n : ℕ) (h1 : σ n u ≤ t) (h2 : t < σ (n + 1) u) :
    idx t u = n := by
  unfold idx
  rw [Nat.find_eq_iff]
  refine ⟨h2, fun m hm => ?_⟩
  push_neg
  exact le_trans ((σ_strictMono u).monotone (show m + 1 ≤ n by omega)) h1

lemma σ_idx_le (t : ℝ) (u : U) (ht : 0 ≤ t) : σ (idx t u) u ≤ t := by
  rcases h : idx t u with _ | n
  · rw [σ_zero]; exact ht
  · have := Nat.find_min (exists_σ_gt t u) (show n < idx t u by omega)
    push_neg at this; exact this

lemma idx_meas (t : ℝ) : Measurable fun u : U => idx t u := by
  unfold idx
  exact measurable_find _ fun k => measurableSet_lt measurable_const (σ_meas (k + 1))

lemma idx_of_nonpos (t : ℝ) (u : U) (ht : t ≤ 0) : idx t u = 0 := by
  unfold idx
  rw [Nat.find_eq_zero]
  exact lt_of_le_of_lt ht (σ_one_pos u)

lemma idx_mono (u : U) : Monotone fun t => idx t u := by
  intro s t hst
  rcases le_or_gt s 0 with hs | hs
  · simp only; rw [idx_of_nonpos s u hs]; exact Nat.zero_le _
  · by_contra hc
    push_neg at hc
    have h1 := σ_idx_le s u hs.le
    have h2 := idx_lt t u
    have := (σ_strictMono u).monotone (show idx t u + 1 ≤ idx s u by omega)
    linarith

/-! ### the jump chain on ℕ: a reflected simple random walk -/

def step (z : ℕ) (b : Bool) : ℕ := if b then z + 1 else (if z = 0 then 1 else z - 1)

lemma step_ne (z : ℕ) (b : Bool) : step z b ≠ z := by
  unfold step; cases b <;> simp <;> split_ifs <;> omega

lemma step_le (z : ℕ) (b : Bool) : step z b ≤ z + 1 := by
  unfold step; cases b <;> simp <;> split_ifs <;> omega

def Yf (x0 : ℕ) (c : Cn) : ℕ → ℕ
  | 0 => x0
  | n + 1 => step (Yf x0 c n) (c n)

lemma Yf_le (x0 : ℕ) (c : Cn) (n : ℕ) : Yf x0 c n ≤ x0 + n := by
  induction n with
  | zero => simp [Yf]
  | succ n ih => simp only [Yf]; have := step_le (Yf x0 c n) (c n); omega

lemma Yf_succ_le (x0 : ℕ) (c : Cn) (n : ℕ) : Yf x0 c (n + 1) ≤ Yf x0 c n + 1 := step_le _ _

lemma Yf_congr (x0 : ℕ) (c c' : Cn) (n : ℕ) (h : ∀ i < n, c i = c' i) :
    Yf x0 c n = Yf x0 c' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Yf]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

lemma Yf_meas (x0 : ℕ) (n : ℕ) : Measurable fun c : Cn => Yf x0 c n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable fun c : Cn => (fun p : ℕ × Bool => step p.1 p.2) (Yf x0 c n, c n)
    exact (measurable_of_countable (fun p : ℕ × Bool => step p.1 p.2)).comp
      (ih.prodMk (measurable_pi_apply n))

def Yc (n : ℕ) (ω : Ωc) : ℕ := Yf ω.2.1 ω.2.2 n

noncomputable def jc (z : ℕ) : PMF ℕ := (PMF.uniformOfFintype Bool).map (step z)

lemma jc_apply (z y : ℕ) : jc z y = ∑ b : Bool, if y = step z b then (2 : ℝ≥0∞)⁻¹ else 0 := by
  unfold jc
  rw [PMF.map_apply, tsum_fintype]
  congr 1; funext b
  simp [PMF.uniformOfFintype_apply]

lemma jc_step_pos (z : ℕ) (b : Bool) : 0 < jc z (step z b) := by
  rw [jc_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun b' : Bool =>
    if step z b = step z b' then (2 : ℝ≥0∞)⁻¹ else 0) (fun _ _ => zero_le) (Finset.mem_univ b))
  simp

lemma jc_irrefl (z : ℕ) : jc z z = 0 := by
  rw [jc_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [if_neg (step_ne z b).symm]

def rc : ℕ → ℝ := fun _ => 1

lemma jt_eq (n : ℕ) (ω : Ωc) : jumpTime rc Yc cl n ω = σ n ω.1 := by
  induction n with
  | zero => simp [jumpTime, σ]
  | succ n ih => simp [jumpTime, ih, σ, Finset.sum_range_succ, rc, cl]

lemma jt_tendsto (ω : Ωc) : Tendsto (fun n => jumpTime rc Yc cl n ω) atTop atTop := by
  simp only [jt_eq]; exact σ_tendsto ω.1

noncomputable def Xc (t : ℝ) (ω : Ωc) : ℕ := Yc (idx t ω.1) ω

lemma Xc_spec (ω : Ωc) (n : ℕ) (t : ℝ) (h1 : jumpTime rc Yc cl n ω ≤ t)
    (h2 : t < jumpTime rc Yc cl (n+1) ω) : Xc t ω = Yc n ω := by
  rw [jt_eq] at h1 h2
  unfold Xc
  rw [idx_eq_of t ω.1 n h1 h2]

lemma Xc_zero (ω : Ωc) : Xc 0 ω = ω.2.1 := by
  unfold Xc; rw [idx_of_nonpos 0 ω.1 le_rfl]; rfl

/-! ### irreducibility -/

lemma stepIter_succ (n : ℕ) (x y : ℕ) :
    stepIter jc (n + 1) x y = ∑' z, jc x z * stepIter jc n z y := by
  simp [stepIter, PMF.bind_apply]

lemma stepIter_ge (n : ℕ) (x z y : ℕ) :
    jc x z * stepIter jc n z y ≤ stepIter jc (n + 1) x y := by
  rw [stepIter_succ]
  exact ENNReal.le_tsum z

lemma stepIter_up (n : ℕ) : ∀ x, 0 < stepIter jc n x (x + n) := by
  induction n with
  | zero => intro x; simp [stepIter]
  | succ n ih =>
    intro x
    have h1 : jc x (step x true) * stepIter jc n (step x true) ((step x true) + n) ≤
        stepIter jc (n + 1) x (x + (n + 1)) := by
      have := stepIter_ge n x (step x true) (x + (n + 1))
      have e : step x true = x + 1 := by simp [step]
      rw [e] at this ⊢
      rwa [show x + 1 + n = x + (n + 1) by ring]
    exact lt_of_lt_of_le (ENNReal.mul_pos (jc_step_pos x true).ne' (ih _).ne') h1

lemma stepIter_down (n : ℕ) : ∀ x, n ≤ x → 0 < stepIter jc n x (x - n) := by
  induction n with
  | zero => intro x _; simp [stepIter]
  | succ n ih =>
    intro x hx
    have e : step x false = x - 1 := by
      simp only [step, Bool.false_eq_true, ↓reduceIte]; rw [if_neg (by omega)]
    have h1 : jc x (step x false) * stepIter jc n (step x false) ((step x false) - n) ≤
        stepIter jc (n + 1) x (x - (n + 1)) := by
      have := stepIter_ge n x (step x false) (x - (n + 1))
      rw [e] at this ⊢
      rwa [show x - 1 - n = x - (n + 1) by omega]
    refine lt_of_lt_of_le (ENNReal.mul_pos (jc_step_pos x false).ne' ?_) h1
    rw [e]; exact (ih (x - 1) (by omega)).ne'

lemma irr : Irreducible jc := by
  intro x y
  rcases le_or_gt x y with h | h
  · refine ⟨y - x, ?_⟩
    have := stepIter_up (y - x) x
    rwa [show x + (y - x) = y by omega] at this
  · refine ⟨x - y, ?_⟩
    have := stepIter_down (x - y) x (by omega)
    rwa [show x - (x - y) = y by omega] at this

/-! ### probabilistic properties of the clocks -/

lemma G_ae' : ∀ᵐ ω ∂(ℙ : Measure Ωc), ω.1 ∈ G := by
  have := G_ae; rw [← map_fst] at this; exact ae_of_ae_map measurable_fst.aemeasurable this

lemma cl_ae (n : ℕ) : (fun ω : Ωc => cl n ω) =ᵐ[ℙ] fun ω => -Real.log (ω.1 n) := by
  filter_upwards [G_ae'] with ω h; simp [cl, Fcl, h]

lemma law_coord (n : ℕ) : (ℙ : Measure Ωc).map (fun ω => ω.1 n) = μU := by
  have : (fun ω : Ωc => ω.1 n) = (fun a : ℕ → ℝ => a n) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_fst, map_fst,
    Measure.infinitePi_map_eval]

lemma cl_exp (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ℙ {ω : Ωc | s < cl n ω} = ENNReal.ofReal (Real.exp (-s)) := by
  have h1 : ℙ {ω : Ωc | s < cl n ω} = ℙ {ω : Ωc | s < -Real.log (ω.1 n)} := by
    apply measure_congr
    filter_upwards [cl_ae n] with ω h
    change (s < cl n ω) = (s < -Real.log (ω.1 n)); rw [h]
  have hA : MeasurableSet {u : ℝ | s < -Real.log u} :=
    measurableSet_lt measurable_const (measurable_id.log.neg)
  have h2 : ℙ {ω : Ωc | s < -Real.log (ω.1 n)} = μU {u : ℝ | s < -Real.log u} := by
    rw [← law_coord n, Measure.map_apply (f := fun ω : Ωc => ω.1 n)
      ((measurable_pi_apply n).comp measurable_fst) hA]; rfl
  rw [h1, h2, μU, Measure.restrict_apply hA]
  have hexp : Real.exp (-s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he : {u : ℝ | s < -Real.log u} ∩ Set.Ioo 0 1 = Set.Ioo 0 (Real.exp (-s)) := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, ?_⟩
      have : Real.log y < -s := by linarith
      exact (Real.log_lt_iff_lt_exp h2).mp this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, by linarith⟩
      have := (Real.log_lt_iff_lt_exp h1).mpr h2
      linarith
  rw [he, Real.volume_Ioo, sub_zero]

lemma iIndep_comp {α α' β : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (h : α → α') (hh : Measurable h)
    (X : ℕ → α' → β) (hX : ∀ i, Measurable (X i)) (H : iIndepFun X (μ.map h)) :
    iIndepFun (fun i ω => X i (h ω)) μ := by
  have : IsProbabilityMeasure (μ.map h) := Measure.isProbabilityMeasure_map hh.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun i ω => X i (h ω))
    (fun i => (hX i).comp hh)]
  have H2 := (iIndepFun_iff_map_fun_eq_infinitePi_map hX).1 H
  rw [Measure.map_map (measurable_pi_iff.2 hX) hh] at H2
  convert H2 using 2
  · rfl
  · funext i
    rw [Measure.map_map (hX i) hh]; rfl

lemma cl_iid : iIndepFun cl (ℙ : Measure Ωc) := by
  rw [iIndepFun_congr (fun n => cl_ae n)]
  refine iIndep_comp (ℙ : Measure Ωc) Prod.fst measurable_fst
    (fun n a => -Real.log (a n)) (fun n => ((measurable_pi_apply n).log).neg) ?_
  rw [map_fst]
  exact iIndepFun_infinitePi (P := fun _ : ℕ => μU) (X := fun _ u => -Real.log u)
    (fun _ => measurable_id.log.neg)

def Fy (p : ℕ × Cn) : ℕ → ℕ := fun n => Yf p.1 p.2 n

lemma indep_cross' : Indep (MeasurableSpace.comap (Prod.fst : Ωc → _) inferInstance)
    (MeasurableSpace.comap (Prod.snd : Ωc → _) ⊤) ℙ := by
  rw [Indep_iff]
  rintro _ _ ⟨A, _, rfl⟩ ⟨B, _, rfl⟩
  have h1 : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B = A ×ˢ B := by ext ω; simp
  have h2 : (Prod.fst ⁻¹' A : Set Ωc) = A ×ˢ Set.univ := by ext ω; simp
  have h3 : (Prod.snd ⁻¹' B : Set Ωc) = Set.univ ×ˢ B := by ext ω; simp
  rw [h1, h2, h3, vol_eq, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ,
    measure_univ, mul_one, one_mul]

lemma cl_indep : Indep (MeasurableSpace.comap (fun ω : Ωc => fun n => cl n ω) inferInstance)
    (MeasurableSpace.comap (fun ω : Ωc => fun n => Yc n ω) ⊤) ℙ := by
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right indep_cross' ?_) ?_
  · show MeasurableSpace.comap (Fy ∘ Prod.snd) ⊤ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  · show MeasurableSpace.comap (Fcl ∘ Prod.fst) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono Fcl_meas.comap_le

/-! ### the Markov property of the jump chain -/

lemma μB_set (s : Set Bool) : μB s = ∑ b, if b ∈ s then (2 : ℝ≥0∞)⁻¹ else 0 := by
  unfold μB
  rw [PMF.toMeasure_apply_fintype]
  congr 1; funext b
  simp [Set.indicator_apply, PMF.uniformOfFintype_apply]

lemma μBpi_eval (n : ℕ) (s : Set Bool) :
    (Measure.infinitePi (fun _ : ℕ => μB)) ((fun c : Cn => c n) ⁻¹' s) = μB s := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => μB) n
  calc _ = ((Measure.infinitePi fun _ : ℕ => μB).map (fun c : Cn => c n)) s := by
        rw [Measure.map_apply (measurable_pi_apply n) MeasurableSet.of_discrete]
    _ = μB s := by rw [h]

lemma coins_indep (n : ℕ) (S1 S2 : Set Cn) (hS1 : ∃ s : Set (↥(Finset.range n) → Bool),
      S1 = (fun c : Cn => fun i : ↥(Finset.range n) => c i) ⁻¹' s)
    (hS2 : ∃ s : Set (↥({n} : Finset ℕ) → Bool),
      S2 = (fun c : Cn => fun i : ↥({n} : Finset ℕ) => c i) ⁻¹' s) :
    (Measure.infinitePi (fun _ : ℕ => μB)) (S1 ∩ S2) =
      (Measure.infinitePi (fun _ : ℕ => μB)) S1 * (Measure.infinitePi (fun _ : ℕ => μB)) S2 := by
  obtain ⟨s, rfl⟩ := hS1
  obtain ⟨s', rfl⟩ := hS2
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => μB) (X := fun _ => (id : Bool → Bool))
    (fun _ => measurable_id)
  have h := hind.indepFun_finset (Finset.range n) {n} (by simp) (fun _ => measurable_pi_apply _)
  exact h.measure_inter_preimage_eq_mul s s' (Set.toFinite s).measurableSet
    (Set.toFinite s').measurableSet

lemma jumpChain : IsJumpChain (Ω := Ωc) jc Yc := by
  intro n path y
  set S1 : Set Cn := {c | ∀ k : Fin (n+1), Yf (path 0) c k = path k} with hS1
  set S2 : Set Cn := {c | step (path (Fin.last n)) (c n) = y} with hS2
  have hzero : ((0 : Fin (n+1)) : ℕ) = 0 := rfl
  have hA : {ω : Ωc | ∀ k : Fin (n+1), Yc k ω = path k} = Set.univ ×ˢ ({path 0} ×ˢ S1) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_singleton_iff,
      hS1]
    constructor
    · intro h
      have h0 : ω.2.1 = path 0 := by have := h 0; rwa [hzero] at this
      refine ⟨h0, fun k => ?_⟩
      have := h k; rwa [Yc, h0] at this
    · rintro ⟨h0, h⟩ k
      rw [Yc, h0]; exact h k
  have hAB : {ω : Ωc | (∀ k : Fin (n+1), Yc k ω = path k) ∧ Yc (n+1) ω = y} =
      Set.univ ×ˢ ({path 0} ×ˢ (S1 ∩ S2)) := by
    ext ω
    have e := congrArg (ω ∈ ·) hA
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_singleton_iff,
      eq_iff_iff] at e
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_singleton_iff,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨h, hy⟩
      obtain ⟨h0, h1⟩ := e.mp h
      refine ⟨h0, h1, ?_⟩
      have hn : Yc n ω = path (Fin.last n) := by have := h (Fin.last n); simpa using this
      show step (path (Fin.last n)) (ω.2.2 n) = y
      rw [← hn]; exact hy
    · rintro ⟨h0, h1, h2⟩
      have h := e.mpr ⟨h0, h1⟩
      refine ⟨h, ?_⟩
      have hn : Yc n ω = path (Fin.last n) := by have := h (Fin.last n); simpa using this
      show step (Yc n ω) (ω.2.2 n) = y
      rw [hn]; exact h2
  rw [hA, hAB, vol_eq, Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul, one_mul,
    μC, Measure.prod_prod, Measure.prod_prod]
  have hind : (Measure.infinitePi (fun _ : ℕ => μB)) (S1 ∩ S2) =
      (Measure.infinitePi (fun _ : ℕ => μB)) S1 * (Measure.infinitePi (fun _ : ℕ => μB)) S2 := by
    apply coins_indep n
    · refine ⟨{g | ∀ k : Fin (n+1), Yf (path 0)
        (fun i => if h : i ∈ Finset.range n then g ⟨i, h⟩ else false) k = path k}, ?_⟩
      ext c
      simp only [hS1, Set.mem_setOf_eq, Set.mem_preimage]
      have : ∀ k : Fin (n+1), Yf (path 0) c k = Yf (path 0)
          (fun i => if h : i ∈ Finset.range n then c i else false) k := by
        intro k
        apply Yf_congr
        intro i hi
        have : i ∈ Finset.range n := Finset.mem_range.mpr (by omega)
        simp [this]
      exact forall_congr' fun k => by rw [this k]
    · exact ⟨{g | step (path (Fin.last n)) (g ⟨n, by simp⟩) = y}, rfl⟩
  have hS2' : (Measure.infinitePi (fun _ : ℕ => μB)) S2 = jc (path (Fin.last n)) y := by
    have : S2 = (fun c : Cn => c n) ⁻¹' {b | step (path (Fin.last n)) b = y} := rfl
    rw [this, μBpi_eval, μB_set, jc_apply]
    congr 1; funext b
    simp only [Set.mem_setOf_eq]
    by_cases hb : step (path (Fin.last n)) b = y
    · rw [if_pos hb, if_pos hb.symm]
    · rw [if_neg hb, if_neg (Ne.symm hb)]
  rw [hind, hS2', mul_assoc]

/-! ### the Markov representation -/

def Nc : ℝ → Ωc → Fin 1 → ℕ := fun _ _ _ => 0
noncomputable def Zc : ℝ → Ωc → Fin 1 → ℕ := fun t ω _ => Xc t ω

noncomputable def Mc : MarkovRepresentation ℕ 1 1 Nc Zc where
  jump := jc
  rate := rc
  Y := Yc
  clock := cl
  X := Xc
  f := fun x => (0, fun _ => x)
  rate_pos := fun _ => by simp [rc]
  jump_irrefl := jc_irrefl
  jump_chain := jumpChain
  clock_pos := cl_pos
  clock_exp := cl_exp
  clock_iid := cl_iid
  clock_indep_jumpChain := cl_indep
  nonexplosive := jt_tendsto
  sample_path := fun ω n t h1 h2 => Xc_spec ω n t h1 h2
  irreducible := irr
  sample_path_eq := fun t ω => rfl
  finite_fiber := fun z => by
    refine (Set.finite_singleton (z 0)).subset ?_
    rintro x ⟨n, hx⟩
    simp only [Prod.mk.injEq] at hx
    rw [Set.mem_singleton_iff, ← hx.2]
  empty_state := ⟨0, by ext <;> simp⟩

lemma spnSize_Mc (x : ℕ) : spnSize Mc x = (x : ℝ) := by
  simp [spnSize, Mc]

def sdc : SPNData 1 1 1 where
  A := fun _ _ => 1
  B := fun _ _ => 1
  b := fun _ => 1
  A_binary := fun _ _ => Or.inr rfl
  B_binary := fun _ _ => Or.inr rfl
  A_col_nonzero := fun _ => ⟨0, rfl⟩
  B_col_nonzero := fun _ => ⟨0, rfl⟩
  b_pos := fun _ => one_pos

def datc : FluidEquationData 1 1 1 :=
  ⟨fun _ _ => 1, fun _ _ => 0, fun _ => 0, fun _ _ => 1, fun _ => 1, fun _ => 0⟩

noncomputable def Ec : Fin 1 → ℝ → Ωc → ℕ := fun _ t ω => idx t ω.1
def vc : Fin 1 → ℕ → Ωc → ℝ := fun _ _ _ => 0
def φc : Fin 1 → ℕ → Ωc → Fin 1 → ℕ := fun _ _ _ _ => 0
def Psic : ℕ → Fin 1 → ℕ → Ωc → ℝ × (Fin 1 → ℕ) := fun _ _ _ _ => (0, 0)

/-- completions of the version started at `x`: `x + E(t) - Z^x(t)` -/
noncomputable def Fcx (x : ℕ) (t : ℝ) (ω : Ωc) (_j : Fin 1) : ℕ :=
  x + idx t ω.1 - Yf x ω.2.2 (idx t ω.1)

/-- buffer contents of the version started at `x` -/
noncomputable def Zcx (x : ℕ) (t : ℝ) (ω : Ωc) (_i : Fin 1) : ℕ := Yf x ω.2.2 (idx t ω.1)

lemma g_mono (x : ℕ) (c : Cn) : Monotone fun n => x + n - Yf x c n := by
  apply monotone_nat_of_le_succ
  intro n
  have h1 := Yf_succ_le x c n
  have h2 := Yf_le x c n
  show x + n - Yf x c n ≤ x + (n + 1) - Yf x c (n + 1)
  omega

lemma Fcx_mono (x : ℕ) (ω : Ωc) (j : Fin 1) : Monotone fun t => Fcx x t ω j :=
  fun a b h => g_mono x ω.2.2 (idx_mono ω.1 h)

lemma Fcx_zero (x : ℕ) (ω : Ωc) : Fcx x 0 ω = 0 := by
  funext j; simp [Fcx, idx_of_nonpos, Yf]

lemma rel (x : ℕ) : SPNRelations sdc Ec vc φc (Mc.f x).1 (Psic x) (Mc.f x).2
    (Fcx x) (Fcx x) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun t ω _ => Fcx x t ω 0)
    (Zcx x) where
  N_init := fun ω => rfl
  Z_init := fun ω => by funext i; simp [Zcx, Mc, idx_of_nonpos, Yf]
  S_init := fun ω => Fcx_zero x ω
  S_mono := Fcx_mono x
  S_rightCont := by
    intro ω j t ht
    refine ⟨σ (idx t ω.1 + 1) ω.1 - t, by linarith [idx_lt t ω.1], ?_⟩
    intro s hs
    simp only [Fcx]
    have : idx s ω.1 = idx t ω.1 :=
      idx_eq_of s ω.1 _ (le_trans (σ_idx_le t ω.1 ht) hs.1) (by linarith [hs.2])
    rw [this]
  F_init := fun ω => Fcx_zero x ω
  F_mono := Fcx_mono x
  service_counts := fun t ω j _ => by simp [Mc]
  departures := fun t ω i _ => by simp [sdc]
  buffer_contents := fun t ω i _ => by
    simp only [Zcx, Mc, Ec, Fcx, cumulativeOutput, delayedTerm, Psic]
    have := Yf_le x ω.2.2 (idx t ω.1)
    rw [Nat.cast_sub this]
    simp [φc]
  availability := fun t ω i _ => by simp
  T_init := fun ω => rfl
  T_mono := fun ω j => monotone_const
  T_capacity := fun ω s t k _ hst => by simp [sdc]; linarith
  service_bound := ⟨0, fun _ _ _ => le_rfl⟩
  effort_completions := fun t ω j _ => by
    simp [delayedWalk, delayedTerm, vc, Mc]

lemma pool_indep_c :
    Indep (MeasurableSpace.comap
      (fun ω : Ωc => fun p : {p // p ∈ (∅ : Finset (Ωc → ℝ × (Fin 1 → ℕ)))} => p.1 ω)
      inferInstance)
      (MeasurableSpace.comap
        (fun ω => (fun i t => Ec i t ω, fun j ℓ => (vc j ℓ ω, φc j ℓ ω))) inferInstance) ℙ := by
  have hc : (fun ω : Ωc => fun p : {p // p ∈ (∅ : Finset (Ωc → ℝ × (Fin 1 → ℕ)))} => p.1 ω) =
      fun _ => fun p => absurd p.2 (Finset.notMem_empty _) := by
    funext ω p; exact absurd p.2 (Finset.notMem_empty _)
  rw [hc, MeasurableSpace.comap_const]
  exact indep_bot_left _

lemma init_set (x : ℕ) : {ω : Ωc | Mc.X 0 ω = x} = Set.univ ×ˢ ({x} ×ˢ Set.univ) := by
  ext ω; simp [Mc, Xc_zero]

lemma init_prob (x : ℕ) : (ℙ : Measure Ωc) {ω | Mc.X 0 ω = x} = πN {x} := by
  rw [init_set, vol_eq, Measure.prod_prod, μC, Measure.prod_prod, measure_univ, measure_univ,
    one_mul, mul_one]

lemma init_supp (x : ℕ) : (ℙ : Measure Ωc) {ω | Mc.X 0 ω = x} ≠ 0 := by
  rw [init_prob]; exact πN_singleton_ne_zero x

lemma init_meas (x : ℕ) : MeasurableSet {ω : Ωc | Mc.X 0 ω = x} := by
  rw [init_set]
  exact MeasurableSet.univ.prod ((measurableSet_singleton x).prod MeasurableSet.univ)

/-- the key decoupling: an event depending only on the clocks and the coins is independent of
the initial state coordinate -/
lemma decouple (x : ℕ) (S : Set (U × Cn)) (hS : MeasurableSet S) :
    (ℙ : Measure Ωc) ({ω | Mc.X 0 ω = x} ∩ {ω | (ω.1, ω.2.2) ∈ S}) =
      πN {x} * (ℙ : Measure Ωc) {ω | (ω.1, ω.2.2) ∈ S} := by
  have hm : Measurable fun ω : Ωc => (ω.1, ω.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hB : MeasurableSet {ω : Ωc | (ω.1, ω.2.2) ∈ S} := hm hS
  rw [vol_eq, Measure.prod_apply ((init_meas x).inter hB), Measure.prod_apply hB]
  have e1 : ∀ u : U, Prod.mk u ⁻¹' ({ω : Ωc | Mc.X 0 ω = x} ∩ {ω | (ω.1, ω.2.2) ∈ S}) =
      {x} ×ˢ {c : Cn | (u, c) ∈ S} := by
    intro u; ext p; simp [Mc, Xc_zero]
  have e2 : ∀ u : U, Prod.mk u ⁻¹' {ω : Ωc | (ω.1, ω.2.2) ∈ S} =
      Set.univ ×ˢ {c : Cn | (u, c) ∈ S} := by
    intro u; ext p; simp
  simp only [e1, e2, μC, Measure.prod_prod, measure_univ, one_mul]
  rw [lintegral_const_mul' _ _ (πN_singleton_ne_top x)]

lemma law_c (x : ℕ) (t : ℝ) (z : Fin 1 → ℕ) :
    (ℙ : Measure Ωc) {ω | Zcx x t ω = z} =
      ((ℙ : Measure Ωc)[|{ω | Mc.X 0 ω = x}]) {ω | Zc t ω = z} := by
  set S : Set (U × Cn) := {p | Yf x p.2 (idx t p.1) = z 0} with hS
  have hSm : MeasurableSet S := by
    have hm : Measurable fun p : U × Cn => Yf x p.2 (idx t p.1) := by
      have h1 : Measurable fun q : Cn × ℕ => Yf x q.1 q.2 :=
        measurable_from_prod_countable_left fun n => Yf_meas x n
      exact h1.comp (measurable_snd.prodMk ((idx_meas t).comp measurable_fst))
    exact hm (measurableSet_singleton (z 0))
  have hZ : {ω : Ωc | Zcx x t ω = z} = {ω | (ω.1, ω.2.2) ∈ S} := by
    ext ω
    simp only [Set.mem_setOf_eq, hS, Zcx, funext_iff, Fin.forall_fin_one]
  have hZ' : {ω : Ωc | Mc.X 0 ω = x} ∩ {ω | Zc t ω = z} =
      {ω | Mc.X 0 ω = x} ∩ {ω | (ω.1, ω.2.2) ∈ S} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hS, Zc, Mc, Xc_zero, funext_iff,
      Fin.forall_fin_one]
    simp only [Xc, Yc]
    constructor
    · rintro ⟨h0, h⟩; rw [h0] at h; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; refine ⟨h0, ?_⟩; rw [h0]; exact h
  rw [cond_apply (init_meas x), hZ', decouple x S hSm, init_prob, hZ, ← mul_assoc,
    ENNReal.inv_mul_cancel (πN_singleton_ne_zero x) (πN_singleton_ne_top x), one_mul]

noncomputable def famc : SPNProcessFamily Mc sdc datc Ec vc φc where
  data_B := rfl
  data_A := rfl
  data_b := rfl
  Psi := Psic
  S := Fcx
  F := Fcx
  Nx := fun _ _ _ _ => 0
  T := fun _ _ _ _ => 0
  D := fun x t ω _ => Fcx x t ω 0
  Zx := Zcx
  relations := rel
  service_bound := ⟨0, fun _ _ _ _ => le_rfl⟩
  pool := ∅
  Psi_mem_pool := fun x j k hk => by simp [Mc] at hk
  pool_indep := pool_indep_c
  initial_support := init_supp
  law := fun x t z _ => law_c x t z

/-! ### the sample point and the refutation -/

noncomputable def u0 : U := fun _ => Real.exp (-1)

lemma u0_mem_G : u0 ∈ G := by
  refine ⟨fun n => ⟨Real.exp_pos _, ?_⟩, fun M => ⟨M, ?_⟩⟩
  · show Real.exp (-1) < 1
    have := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num); simpa using this
  · simp [u0, Real.log_exp]

lemma Fcl_u0 (n : ℕ) : Fcl u0 n = 1 := by
  simp [Fcl, u0_mem_G, u0, Real.log_exp]

lemma σ_u0 (n : ℕ) : σ n u0 = n := by
  simp [σ, Fcl_u0]

lemma idx_u0 (y : ℕ) : idx (y : ℝ) u0 = y := by
  apply idx_eq_of
  · rw [σ_u0]
  · rw [σ_u0]; push_cast; linarith

noncomputable def ω0 : Ωc := (u0, (0, fun _ => true))

lemma hC_univ : ¬ BddAbove ((spnSize Mc) '' (Set.univ : Set ℕ)) := by
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := exists_nat_gt b
  have := hb ⟨m, Set.mem_univ _, spnSize_Mc m⟩
  linarith

lemma uoc_tendsto {d : ℕ} (f : ℕ → ℝ → Fin d → ℝ) (g : ℝ → Fin d → ℝ) (h : UOCConverges f g)
    (i : Fin d) : Tendsto (fun n => f n 1 i) atTop (nhds (g 1 i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nb, hNb⟩ := h 1 zero_le_one ε hε
  exact ⟨Nb, fun n hn => by rw [Real.dist_eq]; exact hNb n hn 1 ⟨zero_le_one, le_rfl⟩ i⟩

end FLECex

open FLECex in
theorem fle_disproof_core : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω]
    {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ) (ω : Ω)
    (C : Set Xstate) (hC : ¬ BddAbove ((spnSize Mrep) '' C))
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)) ∧
        ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
          (nhds (dat.Γ i j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0)),
    ∃ (x : ℕ → Xstate) (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.D (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Dh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * (fam.F (x n) (spnSize Mrep (x n) * t) ω j : ℝ)) Fh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Zh ∧
      IsFluidModelSolution dat Dh Fh Th Zh ∧ (∑ i, Zh 0 i) = 1) := by
  intro h
  have h214 : ∀ i, Tendsto (fun t : ℝ => ((fun _ _ _ => 0 : Fin 1 → ℝ → Ωc → ℕ) i t ω0 : ℝ) / t)
      atTop (nhds (datc.lam i)) := fun i => by simpa [datc] using tendsto_const_nhds
  have h215 : ∀ j, Tendsto (fun n : ℕ =>
        (∑ ℓ ∈ Finset.range n, (fun _ _ _ => 0 : Fin 1 → ℕ → Ωc → ℝ) j ℓ ω0) / n) atTop
        (nhds (datc.m j)) ∧
      ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n,
        ((fun _ _ _ _ => 0 : Fin 1 → ℕ → Ωc → Fin 1 → ℕ) j ℓ ω0 i : ℝ)) / n) atTop
        (nhds (datc.Γ i j)) := fun j =>
    ⟨by simpa [datc] using tendsto_const_nhds, fun i => by simpa [datc] using tendsto_const_nhds⟩
  have h638 : ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ⨆ ℓ ∈ Finset.range n, (fun _ _ _ => 0 : Fin 1 → ℕ → Ωc → ℝ) j ℓ ω0) atTop (nhds 0) :=
    fun j => by simpa using tendsto_const_nhds
  obtain ⟨x, Dh, Fh, Th, Zh, -, hsize, -, -, -, -, hDu, -, -, hZu, hsol, hsum⟩ :=
    @h ℕ _ Ωc _ 1 1 1 Nc Zc Mc sdc datc Ec vc φc famc (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun _ _ _ _ => 0) ω0 Set.univ hC_univ h214 h215 h638
  have hZ := uoc_tendsto _ _ hZu 0
  have hD := uoc_tendsto _ _ hDu 0
  -- eventually `x n ≥ 1`
  have hev : ∀ᶠ n in atTop, (1 : ℝ) ≤ spnSize Mc (x n) := tendsto_atTop.mp hsize 1
  have hrel : ∀ᶠ n in atTop,
      (spnSize Mc (x n))⁻¹ * (famc.Zx (x n) (spnSize Mc (x n) * 1) ω0 0 : ℝ) =
      2 - (spnSize Mc (x n))⁻¹ * (famc.D (x n) (spnSize Mc (x n) * 1) ω0 0 : ℝ) := by
    filter_upwards [hev] with n hn
    rw [spnSize_Mc] at hn ⊢
    have hx : (x n : ℝ) ≠ 0 := by linarith
    simp only [famc, Zcx, Fcx, mul_one, ω0, idx_u0]
    have hle := Yf_le (x n) (fun _ => true) (x n)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
    ring
  have hlim : Zh 1 0 = 2 - Dh 1 0 :=
    tendsto_nhds_unique hZ ((tendsto_const_nhds.sub hD).congr' (hrel.mono fun n hn => hn.symm))
  have h1 := hsol.1 1 zero_le_one 0
  simp only [datc, Fin.sum_univ_one, zero_mul, add_zero, mul_one] at h1
  rw [Fin.sum_univ_one] at hsum
  linarith

end ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability ProcessingNetworks.FluidStability


theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω]
    {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ) (ω : Ω)
    (C : Set Xstate) (hC : ¬ BddAbove ((spnSize Mrep) '' C))
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)) ∧
        ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
          (nhds (dat.Γ i j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0)),
    ∃ (x : ℕ → Xstate) (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.D (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Dh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * (fam.F (x n) (spnSize Mrep (x n) * t) ω j : ℝ)) Fh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Zh ∧
      IsFluidModelSolution dat Dh Fh Th Zh ∧ (∑ i, Zh 0 i) = 1) :=
  ProcessingNetworks.FluidStability.fle_disproof_core
