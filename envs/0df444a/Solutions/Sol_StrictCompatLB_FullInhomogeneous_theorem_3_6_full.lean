-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.theorem_3_6_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:53:45.344259+00:00
-- url     : https://prove2.me/submissions/91511461-77f6-472d-93b7-665219ec0985

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

import Theorems.Thm_StrictCompatLB_Inhomogeneous_random_inhomogeneous_sparse_subcritical
import Theorems.Thm_StrictCompatLB_MeanField_meanfield_limit_and_steady_state
import Theorems.Thm_StrictCompatLB_MeanField_lemma_H_5
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_random_graph_eventually_connected_ae
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_jsqd_kernel_stochastic_and_uniformized_law
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_foster_atom_unique_stationary_and_attracts
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_supermarket_ode_solution_exists_unique
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_fluid_limit_random_initial_law_of_deterministic
import Theorems.Thm_StrictCompatLB_FullInhomogeneous_pure_departure_fluid_limit

set_option autoImplicit false
set_option linter.unusedSectionVars false

section AdaptSec
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SC9aAd
open StrictCompatLB.MeanField StrictCompatLB.FullInhomogeneous

section InfPi
variable {ι : Type*} [Countable ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling coordinate `j` independently leaves the infinite product measure unchanged. -/
lemma map_update_eq (j : ι) :
    ((Measure.infinitePi μ).prod (μ j)).map
        (fun p : (Π i, X i) × X j => Function.update p.1 j p.2) = Measure.infinitePi μ := by
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply measurable_update'
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hj : j ∈ s
  · have hset : (fun p : (Π i, X i) × X j => Function.update p.1 j p.2) ⁻¹' Set.pi (↑s) t
        = Set.pi (↑(s.erase j)) t ×ˢ t j := by
      ext ⟨ω, x⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · have := h i hi.2
          rwa [Function.update_of_ne hi.1] at this
        · have := h j hj
          rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ i hi
        by_cases hij : i = j
        · subst hij
          rwa [Function.update_self]
        · rw [Function.update_of_ne hij]
          exact h1 i ⟨hij, hi⟩
    rw [hset, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i),
      Finset.prod_erase_mul _ _ hj]
  · have hset : (fun p : (Π i, X i) × X j => Function.update p.1 j p.2) ⁻¹' Set.pi (↑s) t
        = Set.pi (↑s) t ×ˢ (Set.univ : Set (X j)) := by
      ext ⟨ω, x⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        and_true]
      constructor
      · intro h i hi
        have := h i hi
        rwa [Function.update_of_ne (by rintro rfl; exact hj hi)] at this
      · intro h i hi
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        exact h i hi
    rw [hset, Measure.prod_prod, measure_univ, mul_one,
      Measure.infinitePi_pi _ (fun i _ => ht i)]

/-- Outer-measure comparison for an arbitrary (possibly non-measurable) cylinder set. -/
lemma le_infinitePi_preimage_eval (j : ι) (A : Set (X j)) :
    μ j A ≤ Measure.infinitePi μ ((fun ω : Π i, X i => ω j) ⁻¹' A) := by
  rw [← measure_toMeasurable ((fun ω : Π i, X i => ω j) ⁻¹' A)]
  have hU : MeasurableSet (toMeasurable (Measure.infinitePi μ)
      ((fun ω : Π i, X i => ω j) ⁻¹' A)) := measurableSet_toMeasurable _ _
  have hmap := map_update_eq μ j
  calc μ j A = (Measure.infinitePi μ).prod (μ j) (Set.univ ×ˢ A) := by
        rw [Measure.prod_prod, measure_univ, one_mul]
    _ ≤ (Measure.infinitePi μ).prod (μ j)
          ((fun p : (Π i, X i) × X j => Function.update p.1 j p.2) ⁻¹'
            toMeasurable (Measure.infinitePi μ) ((fun ω : Π i, X i => ω j) ⁻¹' A)) := by
        apply measure_mono
        rintro ⟨ω, x⟩ ⟨-, hx⟩
        apply subset_toMeasurable
        show Function.update ω j x j ∈ A
        rw [Function.update_self]
        exact hx
    _ = (((Measure.infinitePi μ).prod (μ j)).map
          (fun p : (Π i, X i) × X j => Function.update p.1 j p.2))
          (toMeasurable (Measure.infinitePi μ) ((fun ω : Π i, X i => ω j) ⁻¹' A)) :=
        (Measure.map_apply measurable_update' hU).symm
    _ = _ := by rw [hmap]

end InfPi

lemma iIndepFun_comp_of_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {g : Ω → Ω'} (hg : Measurable g) {ι : Type*} {β : ι → Type*}
    [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω' → β i} (hf : ∀ i, Measurable (f i))
    (h : iIndepFun f (μ.map g)) : iIndepFun (fun i => f i ∘ g) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have key : ∀ T : Set Ω', MeasurableSet T → μ (g ⁻¹' T) = μ.map g T :=
    fun T hT => (Measure.map_apply hg hT).symm
  have e1 : (⋂ i ∈ S, (f i ∘ g) ⁻¹' sets i) = g ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext; simp
  rw [e1, key _ (Finset.measurableSet_biInter S (fun i hi => hf i (hsets i hi))), h S hsets]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Set.preimage_comp, key _ (hf i (hsets i hi))]

lemma indepFun_comp_of_map {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure Ω} {g : Ω → Ω'} (hg : Measurable g) {f₁ : Ω' → β} {f₂ : Ω' → γ}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h : IndepFun f₁ f₂ (μ.map g)) : IndepFun (f₁ ∘ g) (f₂ ∘ g) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have key : ∀ T : Set Ω', MeasurableSet T → μ (g ⁻¹' T) = μ.map g T :=
    fun T hT => (Measure.map_apply hg hT).symm
  try simp only [Set.preimage_comp]
  rw [← Set.preimage_inter, key _ ((hf₁ hs).inter (hf₂ ht)), key _ (hf₁ hs), key _ (hf₂ ht)]
  exact h s t hs ht

/-- A family of point-mass uniformized laws realises, on the infinite product space, one
uniformized process per `N` on a single probability space. -/
theorem process_of_laws {K : (N : ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ} {rate : ℕ → ℝ}
    (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ)))
    [∀ N, IsProbabilityMeasure (P N)] (N : ℕ)
    (hP : IsUniformizedLaw (P N) (K N) (rate N) (fun z => if z = z₀ N then 1 else 0)) :
    IsUniformizedProcess (Measure.infinitePi P) (K N) (rate N) (z₀ N)
      (fun n ω => (ω N).1 n) (fun k ω => (ω N).2 k) := by
  have hev : Measurable (fun ω : Π M, ChainSample (Fin M → ℕ) => ω N) := measurable_pi_apply N
  have hmapev : (Measure.infinitePi P).map (fun ω : Π M, ChainSample (Fin M → ℕ) => ω N) = P N :=
    Measure.infinitePi_map_eval P N
  obtain ⟨_, _, hcyl, hiid, hexp, hind, _⟩ := hP
  refine ⟨inferInstance, fun n => ?_, fun n zs => ?_, fun k => ?_, ?_, fun k => ?_, ?_⟩
  · exact (measurable_pi_apply n).comp (measurable_fst.comp hev)
  · have hS : MeasurableSet {a : ChainSample (Fin N → ℕ) | ∀ j ≤ n, a.1 j = zs j} := by
      have : {a : ChainSample (Fin N → ℕ) | ∀ j ≤ n, a.1 j = zs j}
          = ⋂ j ∈ Set.Iic n, (fun a : ChainSample (Fin N → ℕ) => a.1 j) ⁻¹' {zs j} := by
        ext a; simp
      rw [this]
      exact MeasurableSet.biInter (Set.to_countable _) (fun j _ =>
        (measurableSet_singleton (zs j)).preimage ((measurable_pi_apply j).comp measurable_fst))
    have := Measure.map_apply (μ := Measure.infinitePi P) hev hS
    rw [hmapev, hcyl n zs] at this
    rw [show {ω : Π M, ChainSample (Fin M → ℕ) | ∀ j ≤ n, (ω N).1 j = zs j}
        = (fun ω : Π M, ChainSample (Fin M → ℕ) => ω N) ⁻¹'
          {a : ChainSample (Fin N → ℕ) | ∀ j ≤ n, a.1 j = zs j} from rfl, ← this]
  · exact (measurable_pi_apply k).comp (measurable_snd.comp hev)
  · exact iIndepFun_comp_of_map (f := fun k (a : ChainSample (Fin N → ℕ)) => a.2 k) hev
      (fun k => (measurable_pi_apply k).comp measurable_snd) (by rw [hmapev]; exact hiid)
  · show (Measure.infinitePi P).map ((fun a : ChainSample (Fin N → ℕ) => a.2 k) ∘
        (fun ω : Π M, ChainSample (Fin M → ℕ) => ω N)) = _
    have hmk : Measurable (fun a : ChainSample (Fin N → ℕ) => a.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    rw [← Measure.map_map hmk hev, hmapev]
    exact hexp k
  · exact indepFun_comp_of_map (f₁ := fun a : ChainSample (Fin N → ℕ) => a.1)
      (f₂ := fun a : ChainSample (Fin N → ℕ) => a.2) hev measurable_fst measurable_snd
      (by rw [hmapev]; exact hind)

/-- Transfer of a vanishing probability from the product space to the marginals. -/
theorem tendsto_marginal {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)]
    (P : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (P N)] (A : ∀ N, Set (X N))
    (h : Tendsto (fun N => Measure.infinitePi P ((fun ω : Π M, X M => ω N) ⁻¹' A N))
      atTop (𝓝 0)) :
    Tendsto (fun N => P N (A N)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun N => le_infinitePi_preimage_eval P N (A N))

lemma conn_of_univ (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (hN : 1 ≤ N) (hM : 0 < M N) (h : G N = Finset.univ) : (compatGraph M G N).Connected := by
  haveI : Nonempty (Fin N ⊕ Fin (M N)) := ⟨Sum.inl ⟨0, hN⟩⟩
  have hadj : ∀ v w, (compatGraph M G N).Adj (Sum.inl v) (Sum.inr w) := by
    intro v w
    simp [compatGraph, SimpleGraph.fromRel_adj, h]
  have key : ∀ a, (compatGraph M G N).Reachable a (Sum.inr ⟨0, hM⟩) := by
    rintro (v | w)
    · exact (hadj v _).reachable
    · exact (hadj ⟨0, hN⟩ w).reachable.symm.trans (hadj ⟨0, hN⟩ _).reachable
  exact ⟨fun a b => (key a).trans (key b).symm⟩

lemma nbrW_congr (M : ℕ → ℕ) {G G' : (N : ℕ) → Finset (Fin N × Fin (M N))} {N : ℕ}
    (h : G' N = G N) : nbrW M G' N = nbrW M G N := by
  funext w
  simp only [nbrW, h]

lemma jsqdKernel_congr (lam : ℝ) (d : ℕ) (M : ℕ → ℕ)
    {G G' : (N : ℕ) → Finset (Fin N × Fin (M N))} {N : ℕ}
    (h : G' N = G N) : jsqdKernel lam d M G' N = jsqdKernel lam d M G N := by
  have hr : jsqdRoute M G' N d = jsqdRoute M G N d := by
    funext w z v
    simp only [jsqdRoute, nbrW_congr M h]
  simp only [jsqdKernel, hr]

lemma sparse_patch (M : ℕ → ℕ) {G G' : (N : ℕ) → Finset (Fin N × Fin (M N))} (N₀ : ℕ)
    (hG : ∀ N ≥ N₀, G' N = G N) (h : IsPropSparse M G) : IsPropSparse M G' := by
  intro ε hε δ hδ
  obtain ⟨N₁, hN₁⟩ := h ε hε δ hδ
  refine ⟨max N₀ N₁, fun N hN U => ?_⟩
  rw [nbrW_congr M (hG N (le_of_max_le_left hN))]
  exact hN₁ N (le_of_max_le_right hN) U

lemma isProbVec_point {S : Type*} [DecidableEq S] (z : S) :
    IsProbVec (fun z' : S => if z' = z then (1 : ℝ) else 0) :=
  ⟨fun z' => by dsimp only; split_ifs <;> norm_num, hasSum_ite_eq z 1⟩

/-- Deterministic-initial-state fluid limit on the leaf's eventually connected graph, from the
mean-field theorem (part (i)) applied to the graph patched to be complete below `N₀`. -/
theorem det_fluid_pos (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hconn : ∀ N ≥ N₀, (compatGraph M G N).Connected) (hsparse : IsPropSparse M G)
    (H77 : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' → IsPropSparse M G' →
      ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G' N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0))
    (HK3 : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), ∀ N, 1 ≤ N →
      (compatGraph M G' N).Connected → ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (ChainSample (Fin N → ℕ)),
          IsUniformizedLaw P (jsqdKernel lam d M G' N) ((lam + 1) * (N : ℝ)) μ)
    (q₀ : ℕ → ℝ) (hq₀ : InY q₀) (s : NNReal → ℕ → ℝ) (hs : IsSolution lam d q₀ s)
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
      (∀ N ≥ N₀, IsUniformizedLaw (P N) (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ))
        (fun z => if z = z₀ N then 1 else 0)) →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1
            (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0) := by
  classical
  intro z₀ P hP hz
  set G' : (N : ℕ) → Finset (Fin N × Fin (M N)) :=
    fun N => if N₀ ≤ N then G N else Finset.univ with hG'def
  have hG'eq : ∀ N ≥ N₀, G' N = G N := fun N hN => by simp [hG'def, hN]
  have hG'conn : IsConnectedSeq M G' := by
    intro N hN
    by_cases h : N₀ ≤ N
    · have hc := hconn N h
      rwa [show compatGraph M G' N = compatGraph M G N by
        simp only [compatGraph, hG'eq N h]]
    · exact conn_of_univ M G' N hN (hM N) (by simp [hG'def, h])
  have hG'sparse : IsPropSparse M G' := sparse_patch M N₀ hG'eq hsparse
  have hlaw : ∀ N, ∃ Q : Measure (ChainSample (Fin N → ℕ)), IsProbabilityMeasure Q ∧
      (1 ≤ N → IsUniformizedLaw Q (jsqdKernel lam d M G' N) ((lam + 1) * (N : ℝ))
        (fun z => if z = z₀ N then 1 else 0)) ∧ (N₀ ≤ N → Q = P N) := by
    intro N
    by_cases h : N₀ ≤ N
    · refine ⟨P N, (hP N h).1, fun _ => ?_, fun _ => rfl⟩
      rw [jsqdKernel_congr lam d M (hG'eq N h)]
      exact hP N h
    · by_cases h1 : 1 ≤ N
      · obtain ⟨Q, hQ⟩ := HK3 G' N h1 (hG'conn N h1) _ (isProbVec_point (z₀ N))
        exact ⟨Q, hQ.1, fun _ => hQ, fun h' => absurd h' h⟩
      · exact ⟨Measure.dirac (fun _ _ => 0, fun _ => 0), inferInstance,
          fun h' => absurd h' h1, fun h' => absurd h' h⟩
  choose P' hP'prob hP'law hP'eq using hlaw
  have : ∀ N, IsProbabilityMeasure (P' N) := hP'prob
  have hproc : ∀ N, 1 ≤ N → IsLBProcess (Measure.infinitePi P') lam M N (jsqdRoute M G' N d)
      (z₀ N) (fun n ω => (ω N).1 n) (fun k ω => (ω N).2 k) := fun N hN =>
    process_of_laws (K := fun N => jsqdKernel lam d M G' N) (rate := fun N => (lam + 1) * (N : ℝ))
      z₀ P' N (hP'law N hN)
  have h0 : (fun t => s (Real.toNNReal t)) 0 = q₀ := by
    simp only [Real.toNNReal_zero]; exact hs.1
  have hmain := H77 G' hG'conn hG'sparse z₀ q₀ hq₀ hz (fun t => s (Real.toNNReal t)) hs.2.2.2
    (fun t _ => hs.2.1 _) h0 ((N : ℕ) → ChainSample (Fin N → ℕ)) (Measure.infinitePi P')
    (fun N n ω => (ω N).1 n) (fun N k ω => (ω N).2 k) hproc T hT ε hε
  have hmarg := tendsto_marginal P' (fun N => {a : ChainSample (Fin N → ℕ) | ENNReal.ofReal ε ≤
      PowerOfDUniversality.Fluid.supDistL1
        (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) hmain
  refine hmarg.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [hP'eq N hN]

lemma subcrit_patch (d : ℕ) (M : ℕ → ℕ) {G G' : (N : ℕ) → Finset (Fin N × Fin (M N))} (N₀ : ℕ)
    (hG : ∀ N ≥ N₀, G' N = G N) (h : IsSubcritical d M G) : IsSubcritical d M G' := by
  obtain ⟨γ, h1, h2, h3, h4⟩ := h
  refine ⟨γ, h1, h2, h3, fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := h4 ε hε
  refine ⟨max N₀ N₁, fun N hN v => ?_⟩
  rw [nbrW_congr M (hG N (le_of_max_le_left hN))]
  exact hN₁ N (le_of_max_le_right hN) v

lemma exists_patch (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (N₀ : ℕ) (hconn : ∀ N ≥ N₀, (compatGraph M G N).Connected) :
    ∃ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), (∀ N ≥ N₀, G' N = G N) ∧ IsConnectedSeq M G' := by
  classical
  refine ⟨fun N => if N₀ ≤ N then G N else Finset.univ, fun N hN => by simp [hN], ?_⟩
  intro N hN
  by_cases h : N₀ ≤ N
  · have hc := hconn N h
    rwa [show compatGraph M (fun N => if N₀ ≤ N then G N else Finset.univ) N = compatGraph M G N by
      simp only [compatGraph, h, if_true]]
  · exact conn_of_univ M _ N hN (hM N) (by simp [h])

/-- Steady state for `0 < λ`, from the mean-field theorem (part (ii)) on the patched graph. -/
theorem steady_pos (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N₀ : ℕ)
    (hconn : ∀ N ≥ N₀, (compatGraph M G N).Connected) (hsparse : IsPropSparse M G)
    (hsub : IsSubcritical d M G)
    (H77ii : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsPropSparse M G' → IsSubcritical d M G' →
      ∃ N₁ : ℕ, (∀ N ≥ N₁, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G' N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₁, IsStationary (jsqdKernel lam d M G' N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0)) :
    ∃ N₁ : ℕ, N₀ ≤ N₁ ∧
      (∀ N ≥ N₁, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G N) π) ∧
      ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
        (∀ N ≥ N₁, IsStationary (jsqdKernel lam d M G N) (π N)) →
        ∀ ε : ℝ, 0 < ε →
          Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
              PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
            atTop (𝓝 0) := by
  classical
  obtain ⟨G', hG'eq, hG'conn⟩ := exists_patch M hM G N₀ hconn
  obtain ⟨N₁, hu, hc⟩ := H77ii G' hG'conn (sparse_patch M N₀ hG'eq hsparse)
    (subcrit_patch d M N₀ hG'eq hsub)
  refine ⟨max N₀ N₁, le_max_left _ _, fun N hN => ?_, fun π hπ ε hε => ?_⟩
  · rw [← jsqdKernel_congr lam d M (hG'eq N (le_of_max_le_left hN))]
    exact hu N (le_of_max_le_right hN)
  · have hst : ∀ N, ∃ ρ : (Fin N → ℕ) → ℝ, (N₁ ≤ N → IsStationary (jsqdKernel lam d M G' N) ρ) ∧
        (max N₀ N₁ ≤ N → ρ = π N) := by
      intro N
      by_cases h : max N₀ N₁ ≤ N
      · refine ⟨π N, fun _ => ?_, fun _ => rfl⟩
        rw [jsqdKernel_congr lam d M (hG'eq N (le_of_max_le_left h))]
        exact hπ N h
      · by_cases h1 : N₁ ≤ N
        · obtain ⟨ρ, hρ, -⟩ := hu N h1
          exact ⟨ρ, fun _ => hρ, fun h' => absurd h' h⟩
        · exact ⟨0, fun h' => absurd h' h1, fun h' => absurd h' h⟩
    choose ρ hρst hρeq using hst
    refine (hc ρ (fun N hN => hρst N hN) ε hε).congr' ?_
    filter_upwards [eventually_ge_atTop (max N₀ N₁)] with N hN
    rw [hρeq N hN]

end SC9aAd

end AdaptSec

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField


/-! K4 inputs for a generic load-balancing kernel `lbKernel lam M N route` (any `0 ≤ lam`,
nonnegative routing): rows have finite support, `CGamma` is finite, the empty state has a
self-loop, and every state reaches the empty state. -/

namespace SC9aLP

section rows
variable {S : Type} [DecidableEq S] [Countable S]

omit [DecidableEq S] in
/-- Mixing a probability vector by a stochastic kernel gives a probability vector. -/
theorem mix_hasSum (K : S → S → ℝ) (hK : IsStochasticKernel K) (a : S → ℝ)
    (ha0 : ∀ w, 0 ≤ a w) (ha : HasSum a 1) : HasSum (fun y => ∑' w, a w * K w y) 1 := by
  set f : S × S → ℝ := fun q => a q.2 * K q.2 q.1 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (ha0 _) (hK.1 _ _)
  set g : S × S → ℝ := fun q => a q.1 * K q.1 q.2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (ha0 _) (hK.1 _ _)
  have hrw : ∀ w, ∑' y, g (w, y) = a w := fun w => by
    simp only [hg]; rw [tsum_mul_left, (hK.2 w).tsum_eq, mul_one]
  have hgfib : ∀ w, Summable (fun y => g (w, y)) := fun w => (hK.2 w).summable.mul_left (a w)
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).2 ⟨hgfib, ?_⟩
    simp_rw [hrw]; exact ha.summable
  have hgt : ∑' q, g q = 1 := by
    rw [hgs.tsum_prod' hgfib]; simp_rw [hrw]; exact ha.tsum_eq
  have hfg : f = g ∘ (Equiv.prodComm S S) := by
    funext q; simp [hf, hg]
  have hfs : Summable f := by rw [hfg]; exact hgs.comp_injective (Equiv.prodComm S S).injective
  have hft : ∑' q, f q = 1 := by rw [hfg, ← hgt]; exact (Equiv.prodComm S S).tsum_eq g
  have hfib := (summable_prod_of_nonneg hf0).1 hfs
  rw [hfs.tsum_prod' hfib.1] at hft
  have h2 := hfib.2.hasSum
  rw [hft] at h2
  exact h2

/-- Rows of the `n`-step matrix of a stochastic kernel are probability vectors. -/
theorem stepRow (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n x, (∀ y, 0 ≤ stepProb K n x y) ∧ HasSum (fun y => stepProb K n x y) 1 := by
  intro n
  induction n with
  | zero =>
    intro x
    refine ⟨fun y => ?_, ?_⟩
    · simp only [stepProb]; split_ifs <;> norm_num
    · simp only [stepProb]
      have := hasSum_ite_eq x (1 : ℝ)
      convert this using 1
      funext y; by_cases h : x = y <;> simp [h, eq_comm]
  | succ n ih =>
    intro x
    have hP0 := (ih x).1
    refine ⟨fun y => ?_, ?_⟩
    · show 0 ≤ ∑' w, stepProb K n x w * K w y
      exact tsum_nonneg (fun w => mul_nonneg (hP0 w) (hK.1 _ _))
    · show HasSum (fun y => ∑' w, stepProb K n x w * K w y) 1
      exact mix_hasSum K hK (fun w => stepProb K n x w) hP0 (ih x).2

omit [DecidableEq S] [Countable S] in
theorem kle1 (K : S → S → ℝ) (hK : IsStochasticKernel K) (a b : S) : K a b ≤ 1 :=
  le_hasSum (hK.2 a) b (fun c _ => hK.1 a c)

/-- One more step along a positive edge keeps positivity. -/
theorem step_pos (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (x y y' : S)
    (h1 : 0 < stepProb K n x y) (h2 : 0 < K y y') : 0 < stepProb K (n + 1) x y' := by
  have hP := stepRow K hK n x
  have hs : Summable (fun w => stepProb K n x w * K w y') :=
    Summable.of_nonneg_of_le (fun w => mul_nonneg (hP.1 w) (hK.1 _ _))
      (fun w => by
        have := kle1 K hK w y'
        calc stepProb K n x w * K w y' ≤ stepProb K n x w * 1 :=
              mul_le_mul_of_nonneg_left this (hP.1 w)
          _ = stepProb K n x w := mul_one _) hP.2.summable
  show 0 < ∑' w, stepProb K n x w * K w y'
  exact lt_of_lt_of_le (mul_pos h1 h2)
    (hs.le_tsum y (fun w _ => mul_nonneg (hP.1 w) (hK.1 _ _)))

end rows

variable {M : ℕ → ℕ} {N : ℕ} (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

theorem dep_lb (lam : ℝ) (hlam : 0 ≤ lam) (hr : ∀ w z v, 0 ≤ route w z v)
    (z : Fin N → ℕ) (v : Fin N) :
    1 / (lam + 1) * (1 / (N : ℝ)) ≤ lbKernel lam M N route z (depart z v) := by
  unfold lbKernel
  have hA : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ u : Fin N, route w z u *
        (if depart z v = arrive z u then (1 : ℝ) else 0) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun u _ =>
      mul_nonneg (hr w z u) (by split_ifs <;> norm_num)))
  have hD : (1 : ℝ) ≤ ∑ u : Fin N, (if depart z v = depart z u then (1 : ℝ) else 0) := by
    have := Finset.single_le_sum (f := fun u : Fin N =>
      (if depart z v = depart z u then (1 : ℝ) else 0))
      (fun u _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
    simpa using this
  have hc : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) := by positivity
  nlinarith

theorem dep_pos (lam : ℝ) (hlam : 0 ≤ lam) (hr : ∀ w z v, 0 ≤ route w z v) (hN : 0 < N)
    (z : Fin N → ℕ) (v : Fin N) : 0 < lbKernel lam M N route z (depart z v) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (dep_lb route lam hlam hr z v)

theorem self_pos (lam : ℝ) (hlam : 0 ≤ lam) (hr : ∀ w z v, 0 ≤ route w z v) (hN : 0 < N) :
    0 < lbKernel lam M N route 0 0 := by
  have h := dep_pos route lam hlam hr hN 0 ⟨0, hN⟩
  have h0 : depart (0 : Fin N → ℕ) ⟨0, hN⟩ = 0 := by
    unfold depart; funext u; simp [Function.update_apply]
  rwa [h0] at h

/-- Rows of the kernel have finite support, so every `K z · * V ·` is summable. -/
theorem row_summable (lam : ℝ) (V : (Fin N → ℕ) → ℝ) (z : Fin N → ℕ) :
    Summable (fun z' => lbKernel lam M N route z z' * V z') := by
  classical
  apply summable_of_ne_finset_zero
    (s := Finset.univ.image (arrive z) ∪ Finset.univ.image (depart z))
  intro z' hz'
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
    not_exists] at hz'
  have hk : lbKernel lam M N route z z' = 0 := by
    unfold lbKernel
    have h1 : ∀ u, (if z' = arrive z u then (1 : ℝ) else 0) = 0 :=
      fun u => if_neg (fun h => hz'.1 u h.symm)
    have h2 : ∀ u, (if z' = depart z u then (1 : ℝ) else 0) = 0 :=
      fun u => if_neg (fun h => hz'.2 u h.symm)
    simp [h1, h2]
  rw [hk, zero_mul]

theorem le_Qsum (z : Fin N → ℕ) (v : Fin N) :
    (z v : ℝ) ≤ ∑ i ∈ Finset.Ico 1 (maxLen z + 1), (Qcount z i : ℝ) := by
  have hsub : Finset.Ico 1 (z v + 1) ⊆ Finset.Ico 1 (maxLen z + 1) := by
    apply Finset.Ico_subset_Ico le_rfl
    have : z v ≤ maxLen z := Finset.le_sup (f := z) (Finset.mem_univ v)
    omega
  calc (z v : ℝ) = ∑ i ∈ Finset.Ico 1 (z v + 1), (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.Ico 1 (z v + 1), (Qcount z i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have : 1 ≤ Qcount z i := by
          unfold Qcount
          apply Finset.card_pos.2
          exact ⟨v, by simp; omega⟩
        exact_mod_cast this
    _ ≤ ∑ i ∈ Finset.Ico 1 (maxLen z + 1), (Qcount z i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem CGamma_finite (Γ : ℝ) : (CGamma N Γ).Finite := by
  apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin N => Set.Iic ⌈Γ⌉₊)
    (fun _ => Set.finite_Iic _))
  intro z hz
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
  intro v
  have h1 := le_Qsum z v
  have h2 : (z v : ℝ) ≤ Γ := le_trans h1 hz
  have h3 : (z v : ℝ) ≤ (⌈Γ⌉₊ : ℝ) := h2.trans (Nat.le_ceil Γ)
  exact_mod_cast h3

theorem sum_depart_lt (z : Fin N → ℕ) (v : Fin N) (hv : 0 < z v) :
    ∑ u, depart z v u + 1 = ∑ u, z u := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have hrest : ∑ u ∈ Finset.univ.erase v, depart z v u = ∑ u ∈ Finset.univ.erase v, z u := by
    apply Finset.sum_congr rfl
    intro u hu
    unfold depart
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  rw [hrest]
  unfold depart
  simp only [Function.update_self]
  omega

/-- Every state reaches the empty state. -/
theorem reach_zero (lam : ℝ) (hlam : 0 ≤ lam) (hr : ∀ w z v, 0 ≤ route w z v) (hN : 0 < N)
    (hK : IsStochasticKernel (lbKernel lam M N route)) (z : Fin N → ℕ) :
    ∃ n, 0 < stepProb (lbKernel lam M N route) n z 0 := by
  have key : ∀ k, k ≤ ∑ u, z u → ∃ y : Fin N → ℕ, ∑ u, y u + k = ∑ u, z u ∧
      0 < stepProb (lbKernel lam M N route) k z y := by
    intro k
    induction k with
    | zero => intro _; exact ⟨z, by simp, by simp [stepProb]⟩
    | succ k ih =>
      intro hk
      obtain ⟨y, hy, hpos⟩ := ih (by omega)
      have hne : ∃ v, 0 < y v := by
        by_contra hc
        push Not at hc
        have : ∑ u, y u = 0 := Finset.sum_eq_zero (fun u _ => by have := hc u; omega)
        omega
      obtain ⟨v, hv⟩ := hne
      refine ⟨depart y v, ?_, step_pos _ hK k z y _ hpos (dep_pos route lam hlam hr hN y v)⟩
      have := sum_depart_lt y v hv
      omega
  obtain ⟨y, hy, hpos⟩ := key (∑ u, z u) le_rfl
  have hy0 : y = 0 := by
    have hs : ∑ u, y u = 0 := by omega
    funext u
    have := (Finset.sum_eq_zero_iff.1 hs) u (Finset.mem_univ u)
    simpa using this
  exact ⟨_, hy0 ▸ hpos⟩

theorem lyap_nonneg (k : ℕ) (z : Fin N → ℕ) : 0 ≤ lyap k z := by
  unfold lyap; positivity

end SC9aLP

namespace SC9aL0

variable {M : ℕ → ℕ} {N : ℕ} (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

lemma lb0 (z z' : Fin N → ℕ) :
    lbKernel 0 M N route z z' = 1 / (N : ℝ) * ∑ v, (if z' = depart z v then (1 : ℝ) else 0) := by
  unfold lbKernel; simp

lemma depart_zero (v : Fin N) : depart (0 : Fin N → ℕ) v = 0 := by
  unfold depart; simp

lemma K0_zero (hN : 0 < N) (z' : Fin N → ℕ) :
    lbKernel 0 M N route 0 z' = if z' = 0 then 1 else 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases h : z' = 0
  · simp [lb0, depart_zero, h]; field_simp
  · simp [lb0, depart_zero, h]

theorem stat0 (hN : 0 < N) :
    IsStationary (lbKernel 0 M N route) (fun z => if z = 0 then 1 else 0) := by
  refine ⟨⟨fun z => by dsimp only; split_ifs <;> norm_num, hasSum_ite_eq 0 1⟩, fun z' => ?_⟩
  have : (fun z => (if z = (0 : Fin N → ℕ) then (1 : ℝ) else 0) * lbKernel 0 M N route z z') =
      fun z => if z = 0 then lbKernel 0 M N route 0 z' else 0 := by
    funext z; split_ifs with h <;> simp [h]
  rw [this, K0_zero route hN]
  exact hasSum_ite_eq 0 _

/-- Lyapunov function at `λ = 0`: `N` times the total number of jobs. -/
noncomputable def V0 (N : ℕ) (z : Fin N → ℕ) : ℝ := (N : ℝ) * ∑ v, (z v : ℝ)

lemma V0_nonneg (z : Fin N → ℕ) : 0 ≤ V0 N z := by unfold V0; positivity

lemma hasSum0 (z : Fin N → ℕ) :
    HasSum (fun z' => lbKernel 0 M N route z z' * V0 N z')
      (∑ v, 1 / (N : ℝ) * V0 N (depart z v)) := by
  have : (fun z' => lbKernel 0 M N route z z' * V0 N z') =
      fun z' => ∑ v, (if z' = depart z v then 1 / (N : ℝ) * V0 N (depart z v) else 0) := by
    funext z'
    rw [lb0, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with h <;> simp [h]
  rw [this]
  exact hasSum_sum (fun v _ => hasSum_ite_eq _ _)

lemma sum_depart (z : Fin N → ℕ) (v : Fin N) :
    ∑ u, ((depart z v u : ℕ) : ℝ) = ∑ u, (z u : ℝ) - (if z v = 0 then 0 else 1) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have hrest : ∑ u ∈ Finset.univ.erase v, ((depart z v u : ℕ) : ℝ) =
      ∑ u ∈ Finset.univ.erase v, (z u : ℝ) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have : u ≠ v := Finset.ne_of_mem_erase hu
    simp [depart, Function.update_of_ne this]
  rw [hrest]
  have hv : ((depart z v v : ℕ) : ℝ) = (z v : ℝ) - (if z v = 0 then 0 else 1) := by
    simp only [depart, Function.update_self]
    rcases Nat.eq_zero_or_pos (z v) with h | h
    · simp [h]
    · rw [if_neg h.ne', Nat.cast_sub (by omega)]; simp
  rw [hv]; ring

lemma drift0 (hN : 0 < N) (z : Fin N → ℕ) :
    oneStepDrift (lbKernel 0 M N route) (V0 N) z =
      -((Finset.univ.filter (fun v => z v ≠ 0)).card : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold oneStepDrift kexp
  rw [(hasSum0 route z).tsum_eq]
  simp only [V0, sum_depart]
  rw [Finset.card_filter, Nat.cast_sum]
  have : ∀ v : Fin N, 1 / (N : ℝ) * ((N : ℝ) * (∑ u, (z u : ℝ) - (if z v = 0 then 0 else 1))) =
      ∑ u, (z u : ℝ) - (if z v = 0 then 0 else 1) := by
    intro v; field_simp
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h2 : ∀ v : Fin N, (if z v = 0 then (0 : ℝ) else 1) = (((if z v ≠ 0 then 1 else 0 : ℕ)) : ℝ) := by
    intro v; by_cases h : z v = 0 <;> simp [h]
  simp only [h2]
  ring

theorem drift0_le (hN : 0 < N) (z : Fin N → ℕ) :
    oneStepDrift (lbKernel 0 M N route) (V0 N) z ≤
      -1 + 1 * ({0} : Set (Fin N → ℕ)).indicator (fun _ => (1 : ℝ)) z := by
  rw [drift0 route hN]
  by_cases hz : z = 0
  · subst hz; simp
  · have : ∃ v, z v ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    obtain ⟨v, hv⟩ := this
    have hc : 1 ≤ (Finset.univ.filter (fun v => z v ≠ 0)).card :=
      Finset.card_pos.mpr ⟨v, by simp [hv]⟩
    have : (1 : ℝ) ≤ ((Finset.univ.filter (fun v => z v ≠ 0)).card : ℝ) := by exact_mod_cast hc
    rw [Set.indicator_of_notMem (show z ∉ ({0} : Set (Fin N → ℕ)) from hz)]
    linarith

lemma self0 (hN : 0 < N) : 0 < lbKernel 0 M N route 0 0 := by
  rw [K0_zero route hN]; simp

lemma reach0 : ∀ z ∈ ({0} : Set (Fin N → ℕ)), ∃ n, 0 < stepProb (lbKernel 0 M N route) n z 0 := by
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  exact ⟨0, by subst hz; simp [stepProb]⟩

end SC9aL0


namespace SC9aG
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous StrictCompatLB.FullInhomogeneous
open scoped ENNReal NNReal

theorem jsqdRoute_nonneg (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) : 0 ≤ jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  apply mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  split_ifs <;> positivity

/-- Statement of the K4 child (generic Foster + atom ergodic theorem). -/
def K4Prop : Prop :=
  ∀ {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
      (K : S → S → ℝ), IsStochasticKernel K →
      ∀ (V : S → ℝ), (∀ z, 0 ≤ V z) → (∀ z, Summable (fun z' => K z z' * V z')) →
      ∀ (C : Set S), C.Finite → ∀ b : ℝ,
      (∀ z, oneStepDrift K V z ≤ -1 + b * C.indicator (fun _ => (1 : ℝ)) z) →
      ∀ z₀ : S, 0 < K z₀ z₀ → (∀ z ∈ C, ∃ n, 0 < stepProb K n z z₀) →
      ∀ π : S → ℝ, IsStationary K π →
      ∀ rate : ℝ, 0 < rate →
        (∀ π' : S → ℝ, IsStationary K π' → π' = π) ∧ AttractsAllStates K rate π

/-- Statement of the K3 child. -/
def K3Prop : Prop :=
  ∀ (lam : ℝ), 0 ≤ lam → ∀ (d : ℕ), 1 ≤ d →
    ∀ (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ), 1 ≤ N → 0 < M N →
    (compatGraph M G N).Connected →
    IsStochasticKernel (jsqdKernel lam d M G N) ∧
      ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (ChainSample (Fin N → ℕ)),
          IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ

/-- The deterministic-initial-state fluid limit for every connected sparse graph sequence. -/
def MFiProp (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' → IsPropSparse M G' →
      ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G' N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)

/-- Statement of the K6z child, specialised to `d`, `M`. -/
def ZProp (d : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
    Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
    ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory 0 d s →
    (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P 0 M N (route N) (z₀ N) (Y N) (τ N)) →
      ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
            PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
          atTop (𝓝 0)

/-- Statement of the K6 child. -/
def K6Prop : Prop :=
  ∀ (K : (N : ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ) (rate : ℕ → ℝ) (N₀ : ℕ)
    (q₀ : ℕ → ℝ) (s : ℝ≥0 → ℕ → ℝ) (T ε : ℝ),
    (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
      (∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (fun z => if z = z₀ N then 1 else 0)) →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1
            (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0)) →
    ∀ (μ : (N : ℕ) → (Fin N → ℕ) → ℝ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
    (∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (μ N)) →
    (∀ ε' : ℝ, 0 < ε' → Tendsto (fun N => probOf (μ N)
      {z | ENNReal.ofReal ε' ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀}) atTop (𝓝 0)) →
    Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1
          (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0)

/-- Changing finitely many terms of a sequence of stationary laws. -/
lemma shift {S : ℕ → Type*} (Stat : ∀ N, (S N → ℝ) → Prop) (F : ∀ N, (S N → ℝ) → ℝ)
    (N₁ N₂ : ℕ) (hex : ∀ N ≥ N₁, ∃ ρ, Stat N ρ)
    (h : ∀ π : ∀ N, S N → ℝ, (∀ N ≥ N₁, Stat N (π N)) → Tendsto (fun N => F N (π N)) atTop (𝓝 0)) :
    ∀ π : ∀ N, S N → ℝ, (∀ N ≥ N₂, Stat N (π N)) → Tendsto (fun N => F N (π N)) atTop (𝓝 0) := by
  classical
  intro π hπ
  have : ∀ N, ∃ ρ : S N → ℝ, (N₁ ≤ N → Stat N ρ) ∧ (N₂ ≤ N → ρ = π N) := by
    intro N
    by_cases h2 : N₂ ≤ N
    · exact ⟨π N, fun _ => hπ N h2, fun _ => rfl⟩
    · by_cases h1 : N₁ ≤ N
      · obtain ⟨ρ, hρ⟩ := hex N h1
        exact ⟨ρ, fun _ => hρ, fun h' => absurd h' h2⟩
      · exact ⟨0, fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  choose ρ hρ1 hρ2 using this
  refine (h ρ hρ1).congr' ?_
  filter_upwards [eventually_ge_atTop N₂] with N hN
  rw [hρ2 N hN]

lemma occ_zero_fp (N d : ℕ) (hN : 1 ≤ N) :
    PowerOfDUniversality.Fluid.l1dist (occ (0 : Fin N → ℕ))
      (PowerTwoChoices.Limit.fixedPoint 0 d) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have key : ∀ i, occ (0 : Fin N → ℕ) i = PowerTwoChoices.Limit.fixedPoint 0 d i := by
    intro i
    unfold occ Qcount PowerTwoChoices.Limit.fixedPoint
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hN']
    · have hs : 0 < ∑ k ∈ Finset.range i, d ^ k :=
        Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.2 hi, by simp⟩
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        (fun v _ => by simp only [Pi.zero_apply]; omega)), zero_pow hs.ne']
      simp
  unfold PowerOfDUniversality.Fluid.l1dist
  simp [key]

lemma probOf_delta_zero {N : ℕ} (A : Set (Fin N → ℕ)) (hA : (0 : Fin N → ℕ) ∉ A) :
    probOf (fun z : Fin N → ℕ => if z = 0 then (1 : ℝ) else 0) A = 0 := by
  unfold probOf
  have : A.indicator (fun z : Fin N → ℕ => if z = 0 then (1 : ℝ) else 0) = 0 := by
    funext z
    by_cases hz : z ∈ A
    · have : z ≠ 0 := fun h => hA (h ▸ hz)
      simp [Set.indicator_of_mem hz, this]
    · simp [Set.indicator_of_notMem hz]
  rw [this]
  simp

/-- Steady-state data for `0 < λ`. -/
theorem key_pos (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (hpos : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hsp : IsPropSparse M G) (hsub : IsSubcritical d M G) (Nc : ℕ)
    (hconn0 : ∀ N ≥ Nc, (compatGraph M G N).Connected)
    (HK3 : K3Prop) (HK4 : K4Prop)
    (HMF : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' → IsPropSparse M G' →
      IsSubcritical d M G' →
      ∃ N₁ : ℕ, (∀ N ≥ N₁, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G' N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₁, IsStationary (jsqdKernel lam d M G' N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0))
    (HH5 : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsSubcritical d M G' →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ z : Fin N → ℕ,
        oneStepDrift (jsqdKernel lam d M G' N) (lyap 1) z ≤
          -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
            (fun _ => (1 : ℝ)) z) :
    ∃ N₀ : ℕ, max Nc 1 ≤ N₀ ∧
      (∀ N ≥ N₀, ∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π) ∧
      (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
  classical
  have hc' : ∀ N ≥ max Nc 1, (compatGraph M G N).Connected :=
    fun N hN => hconn0 N (le_of_max_le_left hN)
  obtain ⟨G', hG'eq, hG'conn⟩ := SC9aAd.exists_patch M hM G (max Nc 1) hc'
  obtain ⟨N₁, hN₁, hu, hc⟩ := SC9aAd.steady_pos lam d M hM G (max Nc 1) hc' hsp hsub HMF
  obtain ⟨N₂, -, hdrift⟩ := HH5 G' hG'conn (SC9aAd.subcrit_patch d M (max Nc 1) hG'eq hsub)
  refine ⟨max N₁ N₂, le_trans hN₁ (le_max_left _ _), fun N hN => ?_, fun π hπ ε hε => ?_⟩
  · have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
    have hNc : max Nc 1 ≤ N := le_trans hN₁ hNN₁
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hNc
    obtain ⟨π, hπ, huniq⟩ := hu N hNN₁
    have hK := (HK3 lam hpos.le d (by omega) M G N hN1 (hM N) (hconn0 N (le_of_max_le_left hNc))).1
    have hdr : ∀ z, oneStepDrift (jsqdKernel lam d M G N) (lyap 1) z ≤
        -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
          (fun _ => (1 : ℝ)) z := by
      intro z
      rw [← SC9aAd.jsqdKernel_congr lam d M (hG'eq N hNc)]
      exact hdrift N (le_trans (le_max_right _ _) hN) z
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h4 := HK4 (jsqdKernel lam d M G N) hK (lyap 1) (fun z => SC9aLP.lyap_nonneg 1 z)
      (fun z => SC9aLP.row_summable (M := M) (N := N) (jsqdRoute M G N d) lam (lyap 1) z)
      _ (SC9aLP.CGamma_finite (N := N) _) 2 hdr 0
      (SC9aLP.self_pos (M := M) (N := N) (jsqdRoute M G N d) lam hpos.le
        (jsqdRoute_nonneg M G N d) (by omega))
      (fun z _ => SC9aLP.reach_zero (M := M) (N := N) (jsqdRoute M G N d) lam hpos.le
        (jsqdRoute_nonneg M G N d) (by omega) hK z)
      π hπ ((lam + 1) * (N : ℝ)) (mul_pos (by linarith) hNpos)
    exact ⟨π, hπ, h4.1, h4.2⟩
  · exact shift (S := fun N => Fin N → ℕ) (fun N ρ => IsStationary (jsqdKernel lam d M G N) ρ)
      (fun N ρ => probOf ρ {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) N₁ (max N₁ N₂)
      (fun N hN => (hu N hN).exists) (fun π' hπ' => hc π' hπ' ε hε) π hπ

/-- Steady-state data for `λ = 0`: the empty state is the unique stationary law. -/
theorem key_zero (d : ℕ) (lam : ℝ) (hz : lam = 0)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (Nc : ℕ)
    (hconn0 : ∀ N ≥ Nc, (compatGraph M G N).Connected)
    (HK3 : K3Prop) (HK4 : K4Prop) (hd1 : 1 ≤ d) :
    ∃ N₀ : ℕ, max Nc 1 ≤ N₀ ∧
      (∀ N ≥ N₀, ∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π) ∧
      (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
  classical
  subst hz
  have h0 : ∀ N ≥ max Nc 1,
      IsStationary (jsqdKernel 0 d M G N) (fun z => if z = 0 then 1 else 0) ∧
      (∀ π', IsStationary (jsqdKernel 0 d M G N) π' → π' = (fun z => if z = 0 then 1 else 0)) ∧
      AttractsAllStates (jsqdKernel 0 d M G N) ((0 + 1) * (N : ℝ))
        (fun z => if z = 0 then 1 else 0) := by
    intro N hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hK := (HK3 0 le_rfl d hd1 M G N hN1 (hM N) (hconn0 N (le_of_max_le_left hN))).1
    have hst : IsStationary (jsqdKernel 0 d M G N) (fun z => if z = 0 then 1 else 0) :=
      SC9aL0.stat0 (M := M) (N := N) (jsqdRoute M G N d) (by omega)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h4 := HK4 (jsqdKernel 0 d M G N) hK (SC9aL0.V0 N) (fun z => SC9aL0.V0_nonneg z)
      (fun z => SC9aLP.row_summable (M := M) (N := N) (jsqdRoute M G N d) 0 (SC9aL0.V0 N) z)
      {0} (Set.finite_singleton 0) 1
      (fun z => SC9aL0.drift0_le (M := M) (N := N) (jsqdRoute M G N d) (by omega) z) 0
      (SC9aL0.self0 (M := M) (N := N) (jsqdRoute M G N d) (by omega))
      (SC9aL0.reach0 (M := M) (N := N) (jsqdRoute M G N d))
      _ hst ((0 + 1) * (N : ℝ)) (by linarith)
    exact ⟨hst, h4.1, h4.2⟩
  refine ⟨max Nc 1, le_rfl, fun N hN => ⟨_, h0 N hN⟩, fun π hπ ε hε => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (max Nc 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  rw [(h0 N hN).2.1 (π N) (hπ N hN)]
  symm
  apply probOf_delta_zero
  simp only [Set.mem_setOf_eq, occ_zero_fp N d hN1, not_le]
  exact ENNReal.ofReal_pos.2 hε

theorem core (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hsp : IsPropSparse M G) (hsub : IsSubcritical d M G) (Nc : ℕ)
    (hconn0 : ∀ N ≥ Nc, (compatGraph M G N).Connected)
    (HK3 : K3Prop) (HK4 : K4Prop)
    (HK5 : ∀ (lam : ℝ), 0 ≤ lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
      ∀ q₀ : ℕ → ℝ, InY q₀ → ∃! s : ℝ≥0 → ℕ → ℝ, IsSolution lam d q₀ s)
    (HK6 : K6Prop) (HMFi : 0 < lam → MFiProp lam d M) (HZ : ZProp d M)
    (HMFii : 0 < lam → ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsPropSparse M G' → IsSubcritical d M G' →
      ∃ N₁ : ℕ, (∀ N ≥ N₁, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G' N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₁, IsStationary (jsqdKernel lam d M G' N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0))
    (HH5 : 0 < lam → ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsSubcritical d M G' →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ z : Fin N → ℕ,
        oneStepDrift (jsqdKernel lam d M G' N) (lyap 1) z ≤
          -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
            (fun _ => (1 : ℝ)) z) :
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        (∀ N ≥ N₀,
          (compatGraph M G N).Connected ∧
          IsStochasticKernel (jsqdKernel lam d M G N) ∧
          (∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
            ∃ P : Measure (ChainSample (Fin N → ℕ)),
              IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ) ∧
          (∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π)) ∧
        (∀ q₀ : ℕ → ℝ, InY q₀ →
          ∃ s : ℝ≥0 → ℕ → ℝ,
            IsSolution lam d q₀ s ∧
            (∀ s', IsSolution lam d q₀ s' → s' = s) ∧
            ∀ (μ : (N : ℕ) → (Fin N → ℕ) → ℝ)
              (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
              (∀ N ≥ N₀,
                IsUniformizedLaw (P N) (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) (μ N)) →
              (∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => probOf (μ N)
                  {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀})
                  atTop (𝓝 0)) →
              ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
                  PowerOfDUniversality.Fluid.supDistL1
                    (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T})
                  atTop (𝓝 0)) ∧
        (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N₀, hN₀, hstat, hconc⟩ : ∃ N₀ : ℕ, max Nc 1 ≤ N₀ ∧
      (∀ N ≥ N₀, ∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π) ∧
      (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
    rcases hlam0.lt_or_eq with hpos | hzero
    · exact key_pos d hd lam hpos hlam1 M hM G hsp hsub Nc hconn0 HK3 HK4 (HMFii hpos) (HH5 hpos)
    · exact key_zero d lam hzero.symm M hM G Nc hconn0 HK3 HK4 hd1
  have H77 : MFiProp lam d M := by
    rcases hlam0.lt_or_eq with hpos | hzero
    · exact HMFi hpos
    · subst hzero
      exact fun G' _ _ => HZ (fun N => jsqdRoute M G' N d)
  have hN1 : 1 ≤ N₀ := le_trans (le_max_right _ _) hN₀
  have hconnN : ∀ N ≥ N₀, (compatGraph M G N).Connected :=
    fun N hN => hconn0 N (le_trans (le_max_left _ _) (le_trans hN₀ hN))
  have HK3' : ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), ∀ N, 1 ≤ N →
      (compatGraph M G' N).Connected → ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (ChainSample (Fin N → ℕ)),
          IsUniformizedLaw P (jsqdKernel lam d M G' N) ((lam + 1) * (N : ℝ)) μ :=
    fun G' N hN hc μ hμ => (HK3 lam hlam0 d hd1 M G' N hN (hM N) hc).2 μ hμ
  refine ⟨N₀, hN1, fun N hN => ?_, fun q₀ hq₀ => ?_, hconc⟩
  · have h3 := HK3 lam hlam0 d hd1 M G N (le_trans hN1 hN) (hM N) (hconnN N hN)
    exact ⟨hconnN N hN, h3.1, h3.2, hstat N hN⟩
  · obtain ⟨s, hs, hsu⟩ := HK5 lam hlam0 hlam1 d hd q₀ hq₀
    refine ⟨s, hs, fun s' hs' => hsu s' hs', fun μ P hP hμ T hT ε hε => ?_⟩
    exact HK6 (fun N => jsqdKernel lam d M G N) (fun N => (lam + 1) * (N : ℝ)) N₀ q₀ s T ε
      (SC9aAd.det_fluid_pos lam d M hM G N₀ hN1 hconnN hsp H77 HK3' q₀ hq₀ s hs T hT ε hε)
      μ P hP hμ

theorem main (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω)
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hae1 : ∀ᵐ ω ∂P₀, IsPropSparse M (fun N => graphOf (X N ω)) ∧
      IsSubcritical d M (fun N => graphOf (X N ω)))
    (hae2 : ∀ᵐ ω ∂P₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (compatGraph M (fun N => graphOf (X N ω)) N).Connected)
    (HK3 : K3Prop) (HK4 : K4Prop)
    (HK5 : ∀ (lam : ℝ), 0 ≤ lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
      ∀ q₀ : ℕ → ℝ, InY q₀ → ∃! s : ℝ≥0 → ℕ → ℝ, IsSolution lam d q₀ s)
    (HK6 : K6Prop) (HMFi : 0 < lam → MFiProp lam d M) (HZ : ZProp d M)
    (HMFii : 0 < lam → ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsPropSparse M G' → IsSubcritical d M G' →
      ∃ N₁ : ℕ, (∀ N ≥ N₁, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G' N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₁, IsStationary (jsqdKernel lam d M G' N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0))
    (HH5 : 0 < lam → ∀ G' : (N : ℕ) → Finset (Fin N × Fin (M N)), IsConnectedSeq M G' →
      IsSubcritical d M G' →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ z : Fin N → ℕ,
        oneStepDrift (jsqdKernel lam d M G' N) (lyap 1) z ≤
          -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
            (fun _ => (1 : ℝ)) z) :
    ∀ᵐ ω ∂P₀,
      let G := fun N => graphOf (X N ω)
      IsPropSparse M G ∧ IsSubcritical d M G ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        (∀ N ≥ N₀,
          (compatGraph M G N).Connected ∧
          IsStochasticKernel (jsqdKernel lam d M G N) ∧
          (∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
            ∃ P : Measure (ChainSample (Fin N → ℕ)),
              IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ) ∧
          (∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π)) ∧
        (∀ q₀ : ℕ → ℝ, InY q₀ →
          ∃ s : ℝ≥0 → ℕ → ℝ,
            IsSolution lam d q₀ s ∧
            (∀ s', IsSolution lam d q₀ s' → s' = s) ∧
            ∀ (μ : (N : ℕ) → (Fin N → ℕ) → ℝ)
              (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
              (∀ N ≥ N₀,
                IsUniformizedLaw (P N) (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) (μ N)) →
              (∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => probOf (μ N)
                  {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀})
                  atTop (𝓝 0)) →
              ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
                  PowerOfDUniversality.Fluid.supDistL1
                    (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T})
                  atTop (𝓝 0)) ∧
        (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
  filter_upwards [hae1, hae2] with ω h1 h2
  intro G
  obtain ⟨Nc, hc⟩ := h2
  exact ⟨h1.1, h1.2, core d hd lam hlam0 hlam1 M hM G h1.1 h1.2 Nc hc HK3 HK4 HK5 HK6 HMFi HZ
    HMFii HH5⟩

end SC9aG

open StrictCompatLB.Inhomogeneous StrictCompatLB.FullInhomogeneous ENNReal NNReal in
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ)
    (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h2 : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [IsProbabilityMeasure P₀]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N))
    (hX_law : ∀ N, P₀.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P₀,
      let G := fun N => graphOf (X N ω)
      IsPropSparse M G ∧ IsSubcritical d M G ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        (∀ N ≥ N₀,
          (compatGraph M G N).Connected ∧
          IsStochasticKernel (jsqdKernel lam d M G N) ∧
          (∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
            ∃ P : Measure (ChainSample (Fin N → ℕ)),
              IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ) ∧
          (∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π)) ∧
        (∀ q₀ : ℕ → ℝ, InY q₀ →
          ∃ s : ℝ≥0 → ℕ → ℝ,
            IsSolution lam d q₀ s ∧
            (∀ s', IsSolution lam d q₀ s' → s' = s) ∧
            ∀ (μ : (N : ℕ) → (Fin N → ℕ) → ℝ)
              (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
              (∀ N ≥ N₀,
                IsUniformizedLaw (P N) (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) (μ N)) →
              (∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => probOf (μ N)
                  {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀})
                  atTop (𝓝 0)) →
              ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
                  PowerOfDUniversality.Fluid.supDistL1
                    (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T})
                  atTop (𝓝 0)) ∧
        (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by
  exact SC9aG.main d hd lam hlam0 hlam1 M hM P₀ X
    (StrictCompatLB.Inhomogeneous.random_inhomogeneous_sparse_subcritical d hd M hM p hp_pos hp_le
      h1 h2 h3 P₀ X hX_meas hX_law)
    (StrictCompatLB.FullInhomogeneous.random_graph_eventually_connected_ae M hM p hp_pos hp_le
      h1 h3 P₀ X hX_meas hX_law)
    StrictCompatLB.FullInhomogeneous.jsqd_kernel_stochastic_and_uniformized_law
    @StrictCompatLB.FullInhomogeneous.foster_atom_unique_stationary_and_attracts
    StrictCompatLB.FullInhomogeneous.supermarket_ode_solution_exists_unique
    StrictCompatLB.FullInhomogeneous.fluid_limit_random_initial_law_of_deterministic
    (fun hl G' hc hs =>
      (StrictCompatLB.MeanField.meanfield_limit_and_steady_state lam hl hlam1 d hd M hM G' hc hs).1)
    (StrictCompatLB.FullInhomogeneous.pure_departure_fluid_limit d M hM)
    (fun hl G' hc hs hsb =>
      (StrictCompatLB.MeanField.meanfield_limit_and_steady_state lam hl hlam1 d hd M hM G' hc hs).2
        hsb)
    (fun hl G' hc hsb => StrictCompatLB.MeanField.lemma_H_5 lam hl hlam1 d (by omega) M hM G' hc hsb)
