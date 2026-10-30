-- Prove2me | solution 1 for RelaxedEqMDP.Discrete.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:39:16.813155+00:00
-- url     : https://prove2.me/submissions/f2d2def9-3f34-4dd1-a365-9cbd39bf81a9

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Theorems.Thm_FanGlicksberg_kakutani_fan_glicksberg

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqSolT22
open RelaxedEqMDP.Discrete

/-! ### Stochastic matrices -/

lemma mulVec_bound {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQn : ∀ i j, 0 ≤ Q i j)
    (hQs : ∀ i, ∑ j, Q i j = 1) (v : Fin d → ℝ) (c : ℝ) (hv : ∀ j, |v j| ≤ c) (i : Fin d) :
    |(Q *ᵥ v) i| ≤ c := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, Q i j * v j| ≤ ∑ j, |Q i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, Q i j * c := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (hQn i j)]; exact mul_le_mul_of_nonneg_left (hv j) (hQn i j)
    _ = c := by rw [← Finset.sum_mul, hQs i, one_mul]

lemma listProd_bound {d : ℕ} (L : List (Matrix (Fin d) (Fin d) ℝ))
    (hL : ∀ Q ∈ L, (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 1) (v : Fin d → ℝ) (c : ℝ)
    (hv : ∀ j, |v j| ≤ c) : ∀ i, |(L.prod *ᵥ v) i| ≤ c := by
  induction L with
  | nil => intro i; simpa using hv i
  | cons Q L ih =>
    intro i
    rw [List.prod_cons, ← Matrix.mulVec_mulVec]
    have hQ := hL Q (by simp)
    exact mulVec_bound Q hQ.1 hQ.2 _ c (ih (fun Q' h => hL Q' (by simp [h]))) i

/-! ### Measures carried by `U` -/

lemma integrable_of_contOn {ℓ : ℕ} {U : Set (A ℓ)} (hU : MeasurableSet U) {μ : Measure (A ℓ)}
    [IsFiniteMeasure μ] (hμ : μ Uᶜ = 0) {g : A ℓ → ℝ} (hg : ContinuousOn g U) (C : ℝ)
    (hC : ∀ u ∈ U, |g u| ≤ C) : Integrable g μ := by
  have hae : ∀ᵐ u ∂μ, u ∈ U := ae_iff.2 hμ
  have hres : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem hae
  refine Integrable.of_bound (C := C) ?_ ?_
  · rw [← hres]; exact hg.aestronglyMeasurable hU
  · filter_upwards [hae] with u hu
    simpa [Real.norm_eq_abs] using hC u hu

lemma abs_integral_le {ℓ : ℕ} {U : Set (A ℓ)} {μ : Measure (A ℓ)} [IsProbabilityMeasure μ]
    (hμ : μ Uᶜ = 0) {g : A ℓ → ℝ} (C : ℝ) (hC : ∀ u ∈ U, |g u| ≤ C) :
    |∫ u, g u ∂μ| ≤ C := by
  have hae : ∀ᵐ u ∂μ, u ∈ U := ae_iff.2 hμ
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
    (by filter_upwards [hae] with u hu; simpa [Real.norm_eq_abs] using hC u hu)
  simpa [Real.norm_eq_abs] using this

/-! ### Regularity of the data -/

lemma contOn_f {d ℓ : ℕ} {U : Set (A ℓ)} {p : A ℓ → Matrix (Fin d) (Fin d) ℝ}
    {f : ℕ → Fin d → A ℓ → ℝ} {Theta : ℝ} (h22 : Assumption22 U f p Theta) (t : ℕ) (i : Fin d) :
    ContinuousOn (f t i) U := by
  have hL : LipschitzOnWith (Real.toNNReal Theta) (f t i) U := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ h22.pos.le, Real.dist_eq, dist_eq_norm]
    have h := h22.lip t i x hx y hy
    have h0 : 0 ≤ enorm2 (p x i - p y i) := Real.sqrt_nonneg _
    linarith
  exact hL.continuousOn

lemma abs_le_enorm2 {d : ℕ} (y : Fin d → ℝ) (j : Fin d) : |y j| ≤ enorm2 y := by
  unfold enorm2
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => y j ^ 2)
    (fun j _ => sq_nonneg (y j)) (Finset.mem_univ j))

lemma contOn_p {d ℓ : ℕ} {U : Set (A ℓ)} {p : A ℓ → Matrix (Fin d) (Fin d) ℝ}
    {f : ℕ → Fin d → A ℓ → ℝ} {Theta : ℝ} (h22 : Assumption22 U f p Theta) (i j : Fin d) :
    ContinuousOn (fun u => p u i j) U := by
  have hL : LipschitzOnWith (Real.toNNReal Theta) (fun u => p u i j) U := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ h22.pos.le, Real.dist_eq, dist_eq_norm]
    have h := h22.lip 0 i x hx y hy
    have h1 := abs_le_enorm2 (p x i - p y i) j
    have h0 : 0 ≤ |f 0 i x - f 0 i y| := abs_nonneg _
    simp only [Pi.sub_apply] at h1
    linarith
  exact hL.continuousOn

lemma p_le_one {d ℓ : ℕ} {U : Set (A ℓ)} {p : A ℓ → Matrix (Fin d) (Fin d) ℝ}
    (hS : Standing U p) {u : A ℓ} (hu : u ∈ U) (i j : Fin d) : |p u i j| ≤ 1 := by
  rw [abs_of_nonneg (hS.nonneg u hu i j), ← hS.row_sum u hu i]
  exact Finset.single_le_sum (f := fun j => p u i j) (fun j _ => hS.nonneg u hu i j)
    (Finset.mem_univ j)

/-! ### Averaged quantities for relaxed controls -/

lemma Pbar_stoch {d ℓ : ℕ} {U : Set (A ℓ)} {p : A ℓ → Matrix (Fin d) (Fin d) ℝ}
    {f : ℕ → Fin d → A ℓ → ℝ} {Theta : ℝ} (hS : Standing U p) (h22 : Assumption22 U f p Theta)
    {pol : Control d ℓ} (hpol : IsRelaxed U pol) :
    (∀ i j, 0 ≤ Pbar p pol i j) ∧ ∀ i, ∑ j, Pbar p pol i j = 1 := by
  have hU : MeasurableSet U := hS.compact.isClosed.measurableSet
  constructor
  · intro i j
    haveI := (hpol i).1
    have hae : ∀ᵐ u ∂(pol i), u ∈ U := ae_iff.2 (hpol i).2
    exact integral_nonneg_of_ae (by filter_upwards [hae] with u hu; exact hS.nonneg u hu i j)
  · intro i
    haveI := (hpol i).1
    have hae : ∀ᵐ u ∂(pol i), u ∈ U := ae_iff.2 (hpol i).2
    unfold Pbar
    rw [← integral_finset_sum _ (fun j _ => integrable_of_contOn hU (hpol i).2
      (contOn_p h22 i j) 1 (fun u hu => p_le_one hS hu i j))]
    rw [integral_congr_ae (g := fun _ => (1 : ℝ))
      (by filter_upwards [hae] with u hu; exact hS.row_sum u hu i)]
    simp

lemma fbar_bound {d ℓ : ℕ} {U : Set (A ℓ)} {f : ℕ → Fin d → A ℓ → ℝ} {b : ℕ → ℝ}
    (hb : ∀ t i, ∀ u ∈ U, |f t i u| ≤ b t) {μ : Measure (A ℓ)} [IsProbabilityMeasure μ]
    (hμ : μ Uᶜ = 0) (t : ℕ) (i : Fin d) : |fbar f μ t i| ≤ b t :=
  abs_integral_le hμ (b t) (fun u hu => hb t i u hu)

/-! ### One-step decomposition of the value of `π′ ⊗₁ π` -/

lemma Jseq_concat {d ℓ : ℕ} {U : Set (A ℓ)} {p : A ℓ → Matrix (Fin d) (Fin d) ℝ}
    {f : ℕ → Fin d → A ℓ → ℝ} {Theta : ℝ} (hS : Standing U p) (h22 : Assumption22 U f p Theta)
    {b : ℕ → ℝ} (hbs : Summable b) (hb : ∀ t i, ∀ u ∈ U, |f t i u| ≤ b t)
    {pol pol' : Control d ℓ} (hpol : IsRelaxed U pol) (hpol' : IsRelaxed U pol') (i : Fin d) :
    Jseq p f (concat pol' pol) i = fbar f (pol' i) 0 i + ∑ j, Pbar p pol' i j * V p f pol j := by
  have hst : ∀ m, (∀ a c, 0 ≤ Pbar p (concat pol' pol m) a c) ∧
      ∀ a, ∑ c, Pbar p (concat pol' pol m) a c = 1 := by
    intro m
    by_cases hm : m = 0
    · simp only [concat, hm, if_true]; exact Pbar_stoch hS h22 hpol'
    · simp only [concat, hm, if_false]; exact Pbar_stoch hS h22 hpol
  have hrel : ∀ m, IsRelaxed U (concat pol' pol m) := by
    intro m; by_cases hm : m = 0
    · simp only [concat, hm, if_true]; exact hpol'
    · simp only [concat, hm, if_false]; exact hpol
  have hfb : ∀ (c : Control d ℓ), IsRelaxed U c → ∀ t, ∀ j, |fbar f (c j) t j| ≤ b t := by
    intro c hc t j
    haveI := (hc j).1
    exact fbar_bound hb (hc j).2 t j
  -- the terms
  set T : ℕ → ℝ := fun k => ((List.ofFn (fun m : Fin k => Pbar p (concat pol' pol m))).prod *ᵥ
    (fun j => fbar f ((concat pol' pol k) j) k j)) i with hT
  have hTb : ∀ k, |T k| ≤ b k := by
    intro k
    refine listProd_bound _ ?_ _ (b k) (fun j => hfb _ (hrel k) k j) i
    intro Q hQ
    rw [List.mem_ofFn] at hQ
    obtain ⟨m, rfl⟩ := hQ
    exact hst m
  have hTs : Summable T := Summable.of_norm_bounded hbs (fun k => by
    simpa [Real.norm_eq_abs] using hTb k)
  set W : ℕ → Fin d → ℝ := fun k => (List.ofFn (fun _ : Fin k => Pbar p pol)).prod *ᵥ
    (fun j => fbar f (pol j) (1 + k) j) with hW
  have hWs : ∀ j, Summable (fun k => W k j) := by
    intro j
    have hb1 : Summable (fun k => b (1 + k)) :=
      hbs.comp_injective (fun a c h => by simpa using h)
    refine Summable.of_norm_bounded hb1 (fun k => ?_)
    rw [Real.norm_eq_abs]
    refine listProd_bound _ ?_ _ (b (1 + k)) (fun j => hfb _ hpol (1 + k) j) j
    intro Q hQ
    rw [List.mem_ofFn] at hQ
    obtain ⟨m, rfl⟩ := hQ
    exact Pbar_stoch hS h22 hpol
  have hV : ∀ j, V p f pol j = ∑' k, W k j := fun j => rfl
  have hT0 : T 0 = fbar f (pol' i) 0 i := by
    simp [hT, concat]
  have hTs1 : ∀ k, T (k + 1) = ∑ j, Pbar p pol' i j * W k j := by
    intro k
    simp only [hT, hW]
    rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec]
    have h1 : (fun m : Fin k => Pbar p (concat pol' pol ((Fin.succ m : Fin (k+1)) : ℕ))) =
        fun _ => Pbar p pol := by
      funext m; simp [concat]
    have h2 : (fun j => fbar f ((concat pol' pol (k + 1)) j) (k + 1) j) =
        fun j => fbar f (pol j) (1 + k) j := by
      funext j; simp [concat, add_comm]
    have h3 : concat pol' pol ((0 : Fin (k+1)) : ℕ) = pol' := by simp [concat]
    rw [h1, h2, h3]
    simp [Matrix.mulVec, dotProduct]
  have hJ : Jseq p f (concat pol' pol) i = ∑' k, T k := rfl
  rw [hJ, hTs.tsum_eq_zero_add, hT0]
  simp_rw [hTs1]
  rw [Summable.tsum_finsetSum (fun j _ => (hWs j).mul_left _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, hV]

end RelaxedEqSolT22

namespace RelaxedEqSolT22
open RelaxedEqMDP.Discrete

/-! ### Closed graph with compact range gives upper hemicontinuity -/

lemma uhc_of_graph {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    (Φ : E → Set E) (hsub : ∀ x ∈ K, Φ x ⊆ K)
    (hg : ∀ x ∈ K, ∀ z ∈ K, z ∉ Φ x → ∀ᶠ q in 𝓝 (x, z), q.1 ∈ K → q.2 ∉ Φ q.1) :
    UpperHemicontinuousOn Φ K := by
  refine UpperHemicontinuousOn.of_forall_isOpen ?_
  intro x hx u hu hxu
  have hC : IsCompact (K \ u) := hK.diff hu
  have h := hC.eventually_forall_of_forall_eventually (x₀ := x)
    (P := fun x' z => x' ∈ K → z ∉ Φ x') (fun z hz => hg x hx z hz.1 (fun h => hz.2 (hxu h)))
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds h, self_mem_nhdsWithin] with x' h hx'
  intro z hz
  by_contra hzu
  exact h z ⟨hsub x' hx' hz, hzu⟩ hx' hz

/-! ### The embedding of relaxed controls into a locally convex space -/

/-- `ν ↦ (i, g) ↦ ∫ g dν(i)`. -/
noncomputable def Lmap {d ℓ : ℕ} (U : Set (A ℓ)) (ν : Fin d → ProbabilityMeasure U) :
    Fin d → C(U, ℝ) → ℝ :=
  fun i g => ∫ u, g u ∂(ν i : Measure U)

lemma Lmap_continuous {d ℓ : ℕ} (U : Set (A ℓ)) [CompactSpace U] :
    Continuous (Lmap (d := d) U) := by
  refine continuous_pi fun i => continuous_pi fun g => ?_
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact g)).comp (continuous_apply i)

lemma Lmap_convex {d ℓ : ℕ} (U : Set (A ℓ)) [CompactSpace U] :
    Convex ℝ (Set.range (Lmap (d := d) U)) := by
  rintro _ ⟨ν, rfl⟩ _ ⟨ν', rfl⟩ a b ha hb hab
  refine ⟨fun i => ⟨ENNReal.ofReal a • (ν i : Measure U) + ENNReal.ofReal b • (ν' i : Measure U),
    ⟨?_⟩⟩, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  · funext i g
    have hi1 : Integrable (fun u => g u) (ν i : Measure U) :=
      (BoundedContinuousFunction.mkOfCompact g).integrable _
    have hi2 : Integrable (fun u => g u) (ν' i : Measure U) :=
      (BoundedContinuousFunction.mkOfCompact g).integrable _
    simp only [Lmap, ProbabilityMeasure.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add_measure (hi1.smul_measure ENNReal.ofReal_ne_top)
      (hi2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
    simp [smul_eq_mul]

/-- The averaged transition matrix read off from a point of the embedding space. -/
def Pm {d ℓ : ℕ} {U : Set (A ℓ)} (Pc : Fin d → Fin d → C(U, ℝ)) (x : Fin d → C(U, ℝ) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => x i (Pc i j)

/-- The averaged rewards read off from a point of the embedding space. -/
def fv {d ℓ : ℕ} {U : Set (A ℓ)} (Fc : ℕ → Fin d → C(U, ℝ)) (x : Fin d → C(U, ℝ) → ℝ)
    (t : ℕ) : Fin d → ℝ :=
  fun j => x j (Fc t j)

/-- The continuation value `V` read off from a point of the embedding space. -/
noncomputable def yv {d ℓ : ℕ} {U : Set (A ℓ)} (Pc : Fin d → Fin d → C(U, ℝ))
    (Fc : ℕ → Fin d → C(U, ℝ)) (x : Fin d → C(U, ℝ) → ℝ) : Fin d → ℝ :=
  fun j => ∑' k, ((Pm Pc x ^ k) *ᵥ fv Fc x (1 + k)) j

theorem main {d ℓ : ℕ} (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) :
    ∃ pol : Control d ℓ, IsRelaxedEq U p f pol := by
  obtain ⟨b, hbs, hb⟩ := h21.bound
  have hU : MeasurableSet U := hS.compact.isClosed.measurableSet
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hS.compact
  have hne : U.Nonempty := nonempty_of_measure_ne_zero hS.vol_pos.ne'
  have hfc := contOn_f h22
  have hpc := contOn_p h22
  let Fc : ℕ → Fin d → C(U, ℝ) := fun t i => ⟨U.restrict (f t i), (hfc t i).restrict⟩
  let Pc : Fin d → Fin d → C(U, ℝ) := fun i j => ⟨U.restrict (fun u => p u i j), (hpc i j).restrict⟩
  let K : Set (Fin d → C(U, ℝ) → ℝ) := Set.range (Lmap (d := d) U)
  have hKc : IsCompact K := isCompact_range (Lmap_continuous U)
  have hKconv : Convex ℝ K := Lmap_convex U
  obtain ⟨u0, hu0⟩ := hne
  have hKne : K.Nonempty :=
    ⟨_, Set.mem_range_self (fun _ => (⟨Measure.dirac (⟨u0, hu0⟩ : U), inferInstance⟩ :
      ProbabilityMeasure U))⟩
  -- facts on `K`
  have hKst : ∀ x ∈ K, (∀ i j, 0 ≤ Pm Pc x i j) ∧ ∀ i, ∑ j, Pm Pc x i j = 1 := by
    rintro _ ⟨ν, rfl⟩
    constructor
    · intro i j
      exact integral_nonneg fun u => hS.nonneg u u.2 i j
    · intro i
      simp only [Pm, Lmap]
      have hI : ∀ j ∈ (Finset.univ : Finset (Fin d)),
          Integrable (fun u => Pc i j u) (ν i : Measure U) :=
        fun j _ => (BoundedContinuousFunction.mkOfCompact (Pc i j)).integrable _
      rw [← integral_finsetSum _ hI]
      have h1 : (fun u : U => ∑ j, Pc i j u) = fun _ => (1 : ℝ) :=
        funext fun u => hS.row_sum u u.2 i
      rw [h1]
      simp
  have hKf : ∀ x ∈ K, ∀ t j, |fv Fc x t j| ≤ b t := by
    rintro _ ⟨ν, rfl⟩ t j
    have := norm_integral_le_of_norm_le_const (μ := (ν j : Measure U))
      (f := fun u => Fc t j u) (C := b t)
      (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hb t j u u.2)
    have h1 : (ν j : Measure U).real Set.univ = 1 := by simp
    rw [Real.norm_eq_abs, h1, mul_one] at this
    exact this
  have hb1 : Summable (fun k => b (1 + k)) :=
    hbs.comp_injective (fun a c h => by simpa using h)
  have hPmc : Continuous (Pm (d := d) Pc) :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply (Pc i j)).comp
      (continuous_apply i)
  have hyc : ContinuousOn (yv Pc Fc) K := by
    refine continuousOn_pi.2 fun j => ?_
    refine continuousOn_tsum (u := fun k => b (1 + k)) (fun k => ?_) hb1 (fun k x hx => ?_)
    · have hfv : Continuous fun x => fv Fc x (1 + k) :=
        continuous_pi fun j => (continuous_apply (Fc (1 + k) j)).comp (continuous_apply j)
      exact ((continuous_apply j).comp ((hPmc.pow k).matrix_mulVec hfv)).continuousOn
    · rw [Real.norm_eq_abs, ← List.prod_replicate]
      refine listProd_bound _ ?_ _ (b (1 + k)) (fun j => hKf x hx (1 + k) j) j
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ]
      exact hKst x hx
  -- the best-response correspondence
  let R : (Fin d → C(U, ℝ) → ℝ) → (Fin d → ℝ) → Fin d → ℝ :=
    fun z y i => z i (Fc 0 i) + ∑ m, z i (Pc i m) * y m
  let g : (Fin d → ℝ) → Fin d → A ℓ → ℝ := fun y i u => f 0 i u + ∑ m, p u i m * y m
  let Phi : (Fin d → C(U, ℝ) → ℝ) → Set (Fin d → C(U, ℝ) → ℝ) :=
    fun x => K ∩ {z | ∀ i, ∀ u ∈ U, g (yv Pc Fc x) i u ≤ R z (yv Pc Fc x) i}
  have hgc : ∀ y i, ContinuousOn (g y i) U := fun y i =>
    (hfc 0 i).add (continuousOn_finsetSum _ fun m _ => (hpc i m).mul continuousOn_const)
  have hRc : ∀ y i, Continuous fun z : Fin d → C(U, ℝ) → ℝ => R z y i := by
    intro y i
    have hc : ∀ g0 : C(U, ℝ), Continuous fun z : Fin d → C(U, ℝ) → ℝ => z i g0 :=
      fun g0 => (continuous_apply g0).comp (continuous_apply i)
    exact (hc _).add (continuous_finsetSum _ fun m _ => (hc _).mul continuous_const)
  have hsub : ∀ x ∈ K, Phi x ⊆ K := fun x _ => Set.inter_subset_left
  have hΦne : ∀ x ∈ K, (Phi x).Nonempty := by
    intro x _
    have hmax : ∀ i, ∃ u ∈ U, IsMaxOn (g (yv Pc Fc x) i) U u := fun i =>
      hS.compact.exists_isMaxOn ⟨u0, hu0⟩ (hgc _ i)
    choose uu huu hmx using hmax
    let ν : Fin d → ProbabilityMeasure U := fun i =>
      ⟨Measure.dirac (⟨uu i, huu i⟩ : U), inferInstance⟩
    refine ⟨Lmap U ν, Set.mem_range_self ν, fun i u hu => ?_⟩
    have hR : R (Lmap U ν) (yv Pc Fc x) i = g (yv Pc Fc x) i (uu i) := by
      simp only [R, g, Lmap, ν, ProbabilityMeasure.coe_mk, integral_dirac]
      rfl
    rw [hR]
    exact hmx i hu
  have hRlin : ∀ (y : Fin d → ℝ) i (a c : ℝ) (z1 z2 : Fin d → C(U, ℝ) → ℝ),
      R (a • z1 + c • z2) y i = a * R z1 y i + c * R z2 y i := by
    intro y i a c z1 z2
    simp only [R, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    ring
  have hΦconv : ∀ x ∈ K, Convex ℝ (Phi x) := by
    intro x _
    rintro z1 ⟨hz1K, hz1⟩ z2 ⟨hz2K, hz2⟩ a c ha hc hac
    refine ⟨hKconv hz1K hz2K ha hc hac, fun i u hu => ?_⟩
    rw [hRlin]
    calc g (yv Pc Fc x) i u = a * g (yv Pc Fc x) i u + c * g (yv Pc Fc x) i u := by
          rw [← add_mul, hac, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hz1 i u hu) ha)
          (mul_le_mul_of_nonneg_left (hz2 i u hu) hc)
  have hΦcl : ∀ x ∈ K, IsClosed (Phi x) := by
    intro x _
    refine hKc.isClosed.inter ?_
    have : {z : Fin d → C(U, ℝ) → ℝ | ∀ i, ∀ u ∈ U, g (yv Pc Fc x) i u ≤ R z (yv Pc Fc x) i} =
        ⋂ i, ⋂ u ∈ U, {z | g (yv Pc Fc x) i u ≤ R z (yv Pc Fc x) i} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_biInter fun u _ =>
      isClosed_le continuous_const (hRc _ i)
  have hUHC : UpperHemicontinuousOn Phi K := by
    refine uhc_of_graph hKc Phi hsub ?_
    intro x hx z _ hzn
    have : ∃ i, ∃ u ∈ U, R z (yv Pc Fc x) i < g (yv Pc Fc x) i u := by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      exact hzn ⟨‹z ∈ K›, hcon⟩
    obtain ⟨i, u, hu, hlt⟩ := this
    let H : (Fin d → C(U, ℝ) → ℝ) × (Fin d → C(U, ℝ) → ℝ) → ℝ :=
      fun q => R q.2 (yv Pc Fc q.1) i - g (yv Pc Fc q.1) i u
    have hy1 : ContinuousOn (fun q : (Fin d → C(U, ℝ) → ℝ) × (Fin d → C(U, ℝ) → ℝ) =>
        yv Pc Fc q.1) (K ×ˢ Set.univ) :=
      hyc.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hc2 : ∀ g0 : C(U, ℝ), Continuous fun q : (Fin d → C(U, ℝ) → ℝ) × (Fin d → C(U, ℝ) → ℝ)
        => q.2 i g0 := fun g0 => (continuous_apply g0).comp ((continuous_apply i).comp
          continuous_snd)
    have hy2 : ∀ m, ContinuousOn (fun q : (Fin d → C(U, ℝ) → ℝ) × (Fin d → C(U, ℝ) → ℝ) =>
        yv Pc Fc q.1 m) (K ×ˢ Set.univ) := fun m => (continuous_apply m).comp_continuousOn hy1
    have hH : ContinuousOn H (K ×ˢ Set.univ) := by
      refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) (ContinuousOn.add continuousOn_const ?_)
      · exact (hc2 _).continuousOn
      · exact continuousOn_finsetSum _ fun m _ => (hc2 _).continuousOn.mul (hy2 m)
      · exact continuousOn_finsetSum _ fun m _ => continuousOn_const.mul (hy2 m)
    have hneg : H (x, z) < 0 := by
      show R z (yv Pc Fc x) i - g (yv Pc Fc x) i u < 0
      linarith
    have hev : ∀ᶠ q in 𝓝[K ×ˢ Set.univ] (x, z), H q < 0 :=
      (hH (x, z) ⟨hx, trivial⟩).eventually (gt_mem_nhds hneg)
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with q hq hq1 hmem
    have h1 := hq ⟨hq1, trivial⟩
    have h2 := hmem.2 i u hu
    change R q.2 (yv Pc Fc q.1) i - g (yv Pc Fc q.1) i u < 0 at h1
    linarith
  obtain ⟨x, hxK, hxΦ⟩ := FanGlicksberg.kakutani_fan_glicksberg K hKne hKc hKconv Phi hUHC
    hsub hΦne hΦconv hΦcl
  obtain ⟨ν, rfl⟩ := hxK
  let pol : Control d ℓ := fun i => (ν i : Measure U).map Subtype.val
  have hint : ∀ i (h : A ℓ → ℝ), ∫ u, h u ∂(pol i) = ∫ u, h u ∂(ν i : Measure U) :=
    fun i h => (MeasurableEmbedding.subtype_coe hU).integral_map h
  have hrel : IsRelaxed U pol := by
    intro i
    refine ⟨Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, ?_⟩
    show ((ν i : Measure U).map Subtype.val) Uᶜ = 0
    rw [Measure.map_apply measurable_subtype_coe hU.compl]
    have : (Subtype.val : U → A ℓ) ⁻¹' Uᶜ = ∅ := by ext u; simp [u.2]
    rw [this, measure_empty]
  have hPbar : Pbar p pol = Pm Pc (Lmap U ν) := by
    funext i j
    show ∫ u, p u i j ∂(pol i) = ∫ u, Pc i j u ∂(ν i : Measure U)
    rw [hint]; rfl
  have hfbar : ∀ t j, fbar f (pol j) t j = fv Fc (Lmap U ν) t j := by
    intro t j
    show ∫ u, f t j u ∂(pol j) = ∫ u, Fc t j u ∂(ν j : Measure U)
    rw [hint]; rfl
  have hpow : ∀ k, (List.ofFn fun _ : Fin k => Pbar p pol).prod = Pm Pc (Lmap U ν) ^ k := by
    intro k; rw [List.ofFn_const, List.prod_replicate, hPbar]
  have hVy : V p f pol = yv Pc Fc (Lmap U ν) := by
    funext j
    simp only [V, seqValue, yv, hpow, hfbar]
  refine ⟨pol, hrel, fun i pol' hpol' => ?_⟩
  rw [Jseq_concat hS h22 hbs hb hrel hpol' i]
  have hJ : RelaxedEqMDP.Discrete.J p f pol i = fbar f (pol i) 0 i + ∑ j, Pbar p pol i j * V p f pol j := by
    have : (fun _ : ℕ => pol) = concat pol pol := by funext k; simp [concat]
    unfold RelaxedEqMDP.Discrete.J; rw [this]; exact Jseq_concat hS h22 hbs hb hrel hrel i
  rw [hJ, hVy, hPbar, hfbar]
  set y := yv Pc Fc (Lmap U ν) with hy
  have hcond := hxΦ.2 i
  haveI := (hpol' i).1
  have hae : ∀ᵐ u ∂(pol' i), u ∈ U := ae_iff.2 (hpol' i).2
  have hintf : Integrable (f 0 i) (pol' i) :=
    integrable_of_contOn hU (hpol' i).2 (hfc 0 i) (b 0) (fun u hu => hb 0 i u hu)
  have hintp : ∀ m, Integrable (fun u => p u i m) (pol' i) := fun m =>
    integrable_of_contOn hU (hpol' i).2 (hpc i m) 1 (fun u hu => p_le_one hS hu i m)
  have heq : fbar f (pol' i) 0 i + ∑ j, Pbar p pol' i j * y j = ∫ u, g y i u ∂(pol' i) := by
    simp only [g]
    rw [integral_add hintf (integrable_finset_sum _ fun m _ => (hintp m).mul_const _),
      integral_finset_sum _ (fun m _ => (hintp m).mul_const _)]
    simp_rw [integral_mul_const]
    rfl
  have hle : ∫ u, g y i u ∂(pol' i) ≤ R (Lmap U ν) y i := by
    have hgi : Integrable (g y i) (pol' i) :=
      hintf.add (integrable_finset_sum _ fun m _ => (hintp m).mul_const _)
    calc ∫ u, g y i u ∂(pol' i) ≤ ∫ _, R (Lmap U ν) y i ∂(pol' i) :=
          integral_mono_ae hgi (integrable_const _)
            (by filter_upwards [hae] with u hu; exact hcond u hu)
      _ = R (Lmap U ν) y i := by simp
  have hReq : R (Lmap U ν) y i = fv Fc (Lmap U ν) 0 i + ∑ j, Pm Pc (Lmap U ν) i j * y j := rfl
  rw [heq]
  linarith

end RelaxedEqSolT22

theorem solution {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (RelaxedEqMDP.Discrete.A ℓ))
    (p : RelaxedEqMDP.Discrete.A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → RelaxedEqMDP.Discrete.A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : RelaxedEqMDP.Discrete.Standing U p)
    (h21 : RelaxedEqMDP.Discrete.Assumption21 U f δ)
    (h22 : RelaxedEqMDP.Discrete.Assumption22 U f p Theta)
    (h23 : RelaxedEqMDP.Discrete.Assumption23 U iota vartheta) :
    ∃ pol : RelaxedEqMDP.Discrete.Control d ℓ, RelaxedEqMDP.Discrete.IsRelaxedEq U p f pol :=
  RelaxedEqSolT22.main U p f δ Theta hS h21 h22
