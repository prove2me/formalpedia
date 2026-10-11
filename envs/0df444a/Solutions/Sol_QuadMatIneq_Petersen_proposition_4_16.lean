-- Prove2me | solution 1 for QuadMatIneq.Petersen.proposition_4_16
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:17:05.621577+00:00
-- url     : https://prove2.me/submissions/3f9c8340-4ab7-435c-a3bc-21b936114f72

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

namespace DualityKit

open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

-- K0: pointwise duality to joint minimization
theorem isLeast_add_isGreatest_iff {X : Type*} (S : Set X) (g : X → ℝ)
    (W D : X → Set ℝ) (h : ∀ x ∈ S, ∃ w, IsGreatest (W x) w ∧ IsLeast (D x) w) (q : ℝ) :
    IsLeast {v | ∃ x ∈ S, ∃ w, IsGreatest (W x) w ∧ v = g x + w} q ↔
      IsLeast {v | ∃ x ∈ S, ∃ d ∈ D x, v = g x + d} q := by
  have key : ∀ x ∈ S, ∀ w, IsGreatest (W x) w → IsLeast (D x) w := by
    intro x hx w hw
    obtain ⟨w', hw', hd'⟩ := h x hx
    rw [hw.unique hw']
    exact hd'
  constructor
  · rintro ⟨⟨x, hx, w, hw, rfl⟩, hlow⟩
    refine ⟨⟨x, hx, w, (key x hx w hw).1, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', d', hd', rfl⟩
    obtain ⟨w', hw', hdw'⟩ := h x' hx'
    have h1 := hlow ⟨x', hx', w', hw', rfl⟩
    have h2 := hdw'.2 hd'
    linarith
  · rintro ⟨⟨x, hx, d, hd, rfl⟩, hlow⟩
    obtain ⟨w, hw, hdw⟩ := h x hx
    have h1 := hdw.2 hd
    have h2 := hlow ⟨x, hx, w, hdw.1, rfl⟩
    refine ⟨⟨x, hx, w, hw, by linarith⟩, ?_⟩
    rintro _ ⟨x', hx', w', hw', rfl⟩
    exact hlow ⟨x', hx', w', (key x' hx' w' hw').1, rfl⟩

section aux1cone
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [Fintype G] [DecidableEq G] (u : G → F)

def aux1_coneS (s : Finset G) : Set F :=
  {x | ∃ c : G → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ x = ∑ k, c k • u k}

omit [FiniteDimensional ℝ F] [DecidableEq G] in
lemma aux1_sum_sub_eq (s : Finset G) (c : G → ℝ) (hc : ∀ k ∉ s, c k = 0) :
    ∑ k : s, c k • u k = ∑ k, c k • u k := by
  rw [Finset.sum_coe_sort s (fun k => c k • u k)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by rw [hc k hk, zero_smul])

omit [FiniteDimensional ℝ F] in
lemma aux1_coneS_LI_closed (s : Finset G) (hli : LinearIndependent ℝ (fun k : s => u k)) :
    IsClosed (aux1_coneS u s) := by
  set Λ := Fintype.linearCombination ℝ (fun k : s => u k) with hΛ
  have hker : LinearMap.ker Λ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hΛ, Fintype.linearCombination_apply] at hc
    funext k
    exact Fintype.linearIndependent_iff.1 hli c hc k
  have heq : aux1_coneS u s = Λ '' {c | ∀ k, 0 ≤ c k} := by
    ext x
    constructor
    · rintro ⟨c, hc0, hcs, rfl⟩
      refine ⟨fun k => c k, fun k => hc0 k, ?_⟩
      rw [hΛ, Fintype.linearCombination_apply]
      exact aux1_sum_sub_eq u s c hcs
    · rintro ⟨c, hc0, rfl⟩
      refine ⟨fun k => if h : k ∈ s then c ⟨k, h⟩ else 0, fun k => ?_, fun k hk => ?_, ?_⟩
      · by_cases h : k ∈ s
        · simp only [h, dif_pos]; exact hc0 _
        · simp [h]
      · simp [hk]
      · rw [hΛ, Fintype.linearCombination_apply,
          ← aux1_sum_sub_eq u s _ (fun k hk => by simp [hk])]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp
  have hQ : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext; simp
  rw [heq, hQ]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _
    (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k))

omit [FiniteDimensional ℝ F] in
lemma aux1_cara_step (s : Finset G) (hdep : ¬ LinearIndependent ℝ (fun k : s => u k)) :
    aux1_coneS u s ⊆ ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
  rintro x ⟨c, hc0, hcs, rfl⟩
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  set a0 : G → ℝ := fun k => if h : k ∈ s then g ⟨k, h⟩ else 0 with ha0
  have ha0s : ∀ k ∉ s, a0 k = 0 := fun k hk => by simp [ha0, hk]
  have ha0sum : ∑ k, a0 k • u k = 0 := by
    rw [← aux1_sum_sub_eq u s a0 ha0s, ← hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ha0]
  have ha0i : a0 i ≠ 0 := by simpa [ha0] using hi
  obtain ⟨a, has, hasum, k1, hk1⟩ : ∃ a : G → ℝ, (∀ k ∉ s, a k = 0) ∧ ∑ k, a k • u k = 0 ∧
      ∃ k1, 0 < a k1 := by
    rcases lt_or_gt_of_ne ha0i with h | h
    · refine ⟨-a0, fun k hk => by simp [ha0s k hk], ?_, i, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, ha0sum]
    · exact ⟨a0, ha0s, ha0sum, i, h⟩
  have hk1s : k1 ∈ s := by by_contra h; rw [has k1 h] at hk1; exact lt_irrefl _ hk1
  set P := s.filter (fun k => 0 < a k) with hP
  have hPne : P.Nonempty := ⟨k1, Finset.mem_filter.2 ⟨hk1s, hk1⟩⟩
  obtain ⟨k0, hk0P, hmin⟩ := Finset.exists_min_image P (fun k => c k / a k) hPne
  have hk0 := Finset.mem_filter.1 hk0P
  set t := c k0 / a k0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 k0) hk0.2.le
  refine Set.mem_biUnion hk0.1 ⟨fun k => c k - t * a k, fun k => ?_, fun k hk => ?_, ?_⟩
  · by_cases hak : 0 < a k
    · by_cases hks : k ∈ s
      · have := hmin k (Finset.mem_filter.2 ⟨hks, hak⟩)
        rw [div_le_div_iff₀ hk0.2 hak] at this
        have : t * a k ≤ c k := by
          rw [ht, div_mul_eq_mul_div, div_le_iff₀ hk0.2]; linarith
        linarith
      · rw [has k hks] at hak; exact absurd hak (lt_irrefl _)
    · push Not at hak
      nlinarith [hc0 k]
  · rcases Finset.mem_erase.not.1 hk |> not_and_or.1 with h | h
    · push Not at h; subst h
      show c k - t * a k = 0
      rw [ht, div_mul_cancel₀ _ hk0.2.ne', sub_self]
    · show c k - t * a k = 0
      rw [hcs k h, has k h]; ring
  · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hasum, smul_zero,
      sub_zero]

lemma aux1_coneS_closed : ∀ s : Finset G, IsClosed (aux1_coneS u s) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hli : LinearIndependent ℝ (fun k : s => u k)
    · exact aux1_coneS_LI_closed u s hli
    · have heq : aux1_coneS u s = ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
        refine Set.Subset.antisymm (aux1_cara_step u s hli) ?_
        refine Set.iUnion₂_subset fun k _ => ?_
        rintro x ⟨c, hc0, hcs, rfl⟩
        exact ⟨c, hc0, fun j hj => hcs j (fun h => hj (Finset.mem_of_mem_erase h)), rfl⟩
      rw [heq]
      exact isClosed_biUnion_finset fun k hk => ih _ (Finset.erase_ssubset hk)

end aux1cone

-- K1: closedness of finitely generated cones
/-- Finitely generated cones are closed (the missing Mathlib fact). -/
theorem isClosed_finite_cone {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (u : κ → F) :
    IsClosed {w | ∃ c : κ → ℝ, 0 ≤ c ∧ w = ∑ k, c k • u k} := by
  classical
  have h := aux1_coneS_closed u Finset.univ
  convert h using 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, fun k hk => absurd (Finset.mem_univ k) hk, rfl⟩
  · rintro ⟨c, hc, -, rfl⟩; exact ⟨c, hc, rfl⟩


lemma aux1_linear_pi {α : Type*} [Fintype α] [DecidableEq α] (L : (α → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) :
    L p = ∑ i, p i * L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ L p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma aux1_prod_decomp {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (L : (α → ℝ) × (β → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) (q : β → ℝ) :
    L (p, q) = ∑ i, p i * L (Pi.single i 1, 0) + ∑ j, q j * L (0, Pi.single j 1) := by
  have h1 : L (p, q) = (L ∘ₗ LinearMap.inl ℝ _ _) p + (L ∘ₗ LinearMap.inr ℝ _ _) q := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [h1, aux1_linear_pi, aux1_linear_pi]
  rfl

-- K1: Farkas alternative
/-- Farkas, mixed inequality/equality system, functional form. -/
theorem LP.farkas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) :
    (¬ ∃ x : E, (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j) ↔
      ∃ (y : ι → ℝ) (z : κ → ℝ), 0 ≤ y ∧
        ∑ i, y i • a i + ∑ j, z j • e j = 0 ∧ y ⬝ᵥ b + z ⬝ᵥ d < 0 := by
  classical
  constructor
  · intro hno
    set bas := Module.finBasis ℝ E
    let M : E →ₗ[ℝ] (ι → ℝ) × (κ → ℝ) := (LinearMap.pi a).prod (LinearMap.pi e)
    have hMx : ∀ x, M x = (fun i => a i x, fun j => e j x) := fun x => rfl
    let u : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → (ι → ℝ) × (κ → ℝ) :=
      fun g => match g with
        | Sum.inl i => (Pi.single i 1, 0)
        | Sum.inr (Sum.inl k) => M (bas k)
        | Sum.inr (Sum.inr k) => -M (bas k)
    set S := {w | ∃ c : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → ℝ,
      0 ≤ c ∧ w = ∑ g, c g • u g} with hS
    have hcl : IsClosed S := isClosed_finite_cone u
    have hcv : Convex ℝ S := by
      rintro w1 ⟨c1, h1, rfl⟩ w2 ⟨c2, h2, rfl⟩ s t hs ht _
      refine ⟨s • c1 + t • c2, fun g => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact add_nonneg (mul_nonneg hs (h1 g)) (mul_nonneg ht (h2 g))
      · simp [add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
    have hzero : (0 : (ι → ℝ) × (κ → ℝ)) ∈ S := ⟨0, le_rfl, by simp⟩
    have hsmul : ∀ w ∈ S, ∀ t : ℝ, 0 ≤ t → t • w ∈ S := by
      rintro w ⟨c, hc, rfl⟩ t ht
      refine ⟨t • c, fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ht (hc g)
      · simp [Finset.smul_sum, mul_smul]
    have hgen : ∀ g, u g ∈ S := by
      intro g
      refine ⟨Pi.single g 1, fun h => ?_, ?_⟩
      · by_cases hh : h = g
        · subst hh; simp
        · simp [Pi.single_apply, hh]
      · rw [Finset.sum_eq_single g (fun h _ hh => by simp [Pi.single_apply, hh])
          (fun h => absurd (Finset.mem_univ g) h)]
        simp
    have hM : ∀ x, M x ∈ S := by
      intro x
      refine ⟨fun g => match g with
        | Sum.inl _ => 0
        | Sum.inr (Sum.inl k) => (bas.repr x k)⁺
        | Sum.inr (Sum.inr k) => (bas.repr x k)⁻, fun g => ?_, ?_⟩
      · rcases g with i | k | k
        · exact le_rfl
        · exact posPart_nonneg _
        · exact negPart_nonneg _
      · symm
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, zero_smul, Finset.sum_const_zero, zero_add, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        simp_rw [← sub_smul, posPart_sub_negPart, ← map_smul]
        rw [← map_sum, bas.sum_repr]
    have hnot : (b, d) ∉ S := by
      rintro ⟨c, hc, hbd⟩
      set x := ∑ k, (c (Sum.inr (Sum.inl k)) - c (Sum.inr (Sum.inr k))) • bas k with hx
      have hsum : ∑ g, c g • u g = (fun i => c (Sum.inl i), 0) + M x := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]
        have hMx' : M x = ∑ k, c (Sum.inr (Sum.inl k)) • M (bas k) -
            ∑ k, c (Sum.inr (Sum.inr k)) • M (bas k) := by
          rw [hx]
          simp only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_smul]
        rw [hMx']
        congr 1
        ext i
        · rw [Prod.fst_sum, Finset.sum_apply]; simp [Pi.single_apply]
        · rw [Prod.snd_sum]; simp
      rw [hsum] at hbd
      apply hno
      refine ⟨x, fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrArg Prod.fst hbd) i
        rw [hMx] at this
        simp only [Prod.fst_add, Pi.add_apply] at this
        have h0 : (0:ℝ) ≤ c (Sum.inl i) := hc (Sum.inl i)
        linarith
      · have := congrFun (congrArg Prod.snd hbd) j
        rw [hMx] at this
        simp only [Prod.snd_add, Pi.add_apply, Prod.snd_zero, Pi.zero_apply, zero_add] at this
        exact this.symm
    obtain ⟨Fl, s, hFw, hFb⟩ := geometric_hahn_banach_point_closed hcv hcl hnot
    have hs0 : s < 0 := by simpa using hFb 0 hzero
    have hFnn : ∀ w ∈ S, 0 ≤ Fl w := by
      intro w hw
      by_contra hneg
      push Not at hneg
      have hmem := hsmul w hw (s / Fl w) (div_nonneg_of_nonpos hs0.le hneg.le)
      have := hFb _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    have hFM : ∀ x, Fl (M x) = 0 := by
      intro x
      have h1 := hFnn _ (hM x)
      have h2 := hFnn _ (hM (-x))
      rw [map_neg, map_neg] at h2
      linarith
    have hdec := aux1_prod_decomp (Fl : (ι → ℝ) × (κ → ℝ) →L[ℝ] ℝ).toLinearMap
    refine ⟨fun i => Fl (Pi.single i 1, 0), fun j => Fl (0, Pi.single j 1),
      fun i => hFnn _ (hgen (Sum.inl i)), ?_, ?_⟩
    · ext x
      have := hFM x
      rw [hMx] at this
      have h2 := hdec (fun i => a i x) (fun j => e j x)
      simp only [ContinuousLinearMap.coe_coe] at h2
      rw [this] at h2
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply]
      rw [h2]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · have h2 := hdec b d
      simp only [ContinuousLinearMap.coe_coe] at h2
      have : Fl (b, d) < 0 := hFw.trans hs0
      rw [h2] at this
      simp only [dotProduct]
      convert this using 2 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rintro ⟨y, z, hy, hsum, hneg⟩ ⟨x, hax, hex⟩
    have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply, hex] at h
    have hle : ∑ i, y i * a i x ≤ ∑ i, y i * b i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
    simp only [dotProduct] at hneg
    linarith


-- K2: primal feasible set
/-- Primal: maximize `c x` subject to `a i x ≤ b i`, `e j x = d j` (`x` free in `E`). -/
def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

-- K2: dual feasible set
/-- Dual: `y ≥ 0`, `z` free, `Σ yᵢ aᵢ + Σ zⱼ eⱼ = c`; objective `y ⬝ᵥ b + z ⬝ᵥ d` (minimize). -/
def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

-- K2: weak duality
theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith


/-- The dual constraint map `(y, z) ↦ Σ yᵢ aᵢ + Σ zⱼ eⱼ`. -/
def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

/-- The dual objective `(y, z) ↦ y ⬝ᵥ b + z ⬝ᵥ d`. -/
def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

-- K2: strong duality with attainment
/-- Both feasible ⇒ both optima attained and equal. (No constraint qualification needed.) -/
theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

-- K2: bounded primal gives dual feasibility
/-- Primal feasible and bounded ⇒ dual feasible. -/
theorem LP.dualFeas_nonempty_of_bddAbove
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) : (LP.DualFeas a e c).Nonempty := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨yz, hyz, -⟩ := aux1_alt a b e d c hP (M + 1) fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    linarith
  exact ⟨yz, hyz⟩

-- K2: infeasible primal gives unbounded dual
/-- Primal infeasible, dual feasible ⇒ dual unbounded below. -/
theorem LP.not_bddBelow_dual_of_infeasible
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : LP.Feas a b e d = ∅)
    (hD : (LP.DualFeas a e c).Nonempty) :
    ¬ BddBelow ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) := by
  rintro ⟨L, hL⟩
  obtain ⟨y0, z0, hy0, hsum0, hneg0⟩ := (LP.farkas a b e d).1 (by
    rintro ⟨x, hx⟩
    have : x ∈ LP.Feas a b e d := hx
    rw [hP] at this
    exact this)
  obtain ⟨yz, hy, hsum⟩ := hD
  have hLle : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := hL ⟨yz, ⟨hy, hsum⟩, rfl⟩
  set g := y0 ⬝ᵥ b + z0 ⬝ᵥ d with hg
  set t := (yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) / (-g) with ht
  have hgpos : 0 < -g := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hgpos.le
  have htg : t * g = -(yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff hgpos.ne']; ring
  have hmem : (yz.1 + t • y0, yz.2 + t • z0) ∈ LP.DualFeas a e c := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : (0:ℝ) ≤ yz.1 i := hy i
      have h2 : (0:ℝ) ≤ y0 i := hy0 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, ← Finset.smul_sum]
      calc _ = (∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j) +
            t • (∑ i, y0 i • a i + ∑ j, z0 j • e j) := by rw [smul_add]; abel
        _ = c := by rw [hsum, hsum0, smul_zero, add_zero]
  have := hL ⟨_, hmem, rfl⟩
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
  have : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d + t * g := by rw [hg]; linarith
  linarith

-- K2: EReal value form
/-- EReal value form: equal unless both sides are infeasible (then `⊥ ≠ ⊤`). -/
theorem LP.ereal_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (h : (LP.Feas a b e d).Nonempty ∨ (LP.DualFeas a e c).Nonempty) :
    ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) =
      ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) := by
  by_cases hP : (LP.Feas a b e d).Nonempty <;> by_cases hD : (LP.DualFeas a e c).Nonempty
  · obtain ⟨v, ⟨⟨x, hx, hxv⟩, hvub⟩, ⟨⟨yz, hyz, hyzv⟩, hvlb⟩⟩ :=
      LP.strong_duality a b e d c hP hD
    have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm (iSup₂_le fun x' hx' => EReal.coe_le_coe_iff.2 (hvub ⟨x', hx', rfl⟩)) ?_
      exact le_iSup₂_of_le x hx (by rw [hxv])
    have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm ?_ (le_iInf₂ fun yz' hyz' => EReal.coe_le_coe_iff.2
        (hvlb ⟨yz', hyz', rfl⟩))
      exact iInf₂_le_of_le yz hyz (by rw [← hyzv])
    rw [hL, hR]
  · have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = ⊤ := by
      refine iInf₂_eq_top.2 fun yz hyz => absurd ⟨yz, hyz⟩ hD
    rw [hR, EReal.eq_top_iff_forall_lt]
    intro r
    have hnb : ¬ BddAbove (c '' LP.Feas a b e d) := fun hb =>
      hD (LP.dualFeas_nonempty_of_bddAbove a b e d c hP hb)
    rw [not_bddAbove_iff] at hnb
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hnb r
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlt) (le_iSup₂_of_le x hx le_rfl)
  · have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = ⊥ := by
      refine iSup₂_eq_bot.2 fun x hx => absurd ⟨x, hx⟩ hP
    rw [hL, eq_comm, EReal.eq_bot_iff_forall_lt]
    intro r
    have hnb := LP.not_bddBelow_dual_of_infeasible a b e d c
      (Set.not_nonempty_iff_eq_empty.1 hP) hD
    rw [not_bddBelow_iff] at hnb
    obtain ⟨_, ⟨yz, hyz, rfl⟩, hlt⟩ := hnb r
    exact lt_of_le_of_lt (iInf₂_le_of_le yz hyz le_rfl) (EReal.coe_lt_coe_iff.2 hlt)
  · exact absurd h (by tauto)


/-- The functional `v ↦ u ⬝ᵥ v`. -/
def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

lemma aux1_dotL_apply {n : Type*} [Fintype n] (u v : n → ℝ) : aux1_dotL u v = u ⬝ᵥ v := rfl

lemma aux1_dotL_inj {n : Type*} [Fintype n] {u w : n → ℝ} (h : aux1_dotL u = aux1_dotL w) :
    u = w := by
  classical
  funext j
  have := congrArg (fun φ : Module.Dual ℝ (n → ℝ) => φ (Pi.single j 1)) h
  simpa [aux1_dotL_apply, dotProduct_single] using this

lemma aux1_sum_dotL {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (y : m → ℝ) :
    ∑ i, y i • aux1_dotL (A i) = aux1_dotL (Aᵀ *ᵥ y) := by
  ext v
  rw [LinearMap.sum_apply, aux1_dotL_apply, mulVec_transpose, ← dotProduct_mulVec]
  simp only [LinearMap.smul_apply, smul_eq_mul, aux1_dotL_apply, dotProduct]
  rfl

lemma aux1_matFeas {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) :
    x ∈ LP.Feas (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim) ↔
      A *ᵥ x ≤ b :=
  ⟨fun h i => h.1 i, fun h => ⟨fun i => h i, fun j => j.elim⟩⟩

lemma aux1_matDual {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ)
    (yz : (m → ℝ) × (Empty → ℝ)) :
    yz ∈ LP.DualFeas (fun i => aux1_dotL (A i)) (fun j : Empty => j.elim) (aux1_dotL c) ↔
      0 ≤ yz.1 ∧ Aᵀ *ᵥ yz.1 = c := by
  simp only [LP.DualFeas, Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    aux1_sum_dotL]
  exact and_congr Iff.rfl ⟨aux1_dotL_inj, fun h => by rw [h]⟩

-- K2 (matrix corollary): strong duality for `max c⬝x, A x ≤ b`
theorem LP.strong_duality_matrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      (∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ c ⬝ᵥ x) := by
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨y0, hy0, hy0c⟩ := hD
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, hub⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim)
      (aux1_dotL c) ⟨x0, (aux1_matFeas A b x0).2 hx0⟩
      ⟨(y0, fun j => j.elim), (aux1_matDual A c _).2 ⟨hy0, hy0c⟩⟩
  obtain ⟨hy, hyc⟩ := (aux1_matDual A c yz).1 hyz
  refine ⟨x, yz.1, (aux1_matFeas A b x).1 hx, hy, hyc, ?_, fun x' hx' => ?_⟩
  · rw [aux1_dotL_apply] at hxv
    have h0 : yz.2 ⬝ᵥ (fun j : Empty => j.elim) = 0 := by simp [dotProduct]
    simp only [h0, add_zero] at hyzv
    rw [hxv, ← hyzv, dotProduct_comm]
  · have := hub ⟨x', (aux1_matFeas A b x').2 hx', rfl⟩
    rw [← hxv] at this
    exact this

-- K2 (matrix corollary): bounded polyhedron gives dual feasibility
/-- A nonempty bounded polyhedron has a feasible dual for every cost. -/
theorem LP.exists_dual_of_isBounded {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (hne : {x | A *ᵥ x ≤ b}.Nonempty)
    (hbd : Bornology.IsBounded {x | A *ᵥ x ≤ b}) (c : n → ℝ) :
    ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨yz, hyz⟩ := LP.dualFeas_nonempty_of_bddAbove (fun i => aux1_dotL (A i)) b
    (fun j : Empty => j.elim) (fun j => j.elim) (aux1_dotL c)
    ⟨x0, (aux1_matFeas A b x0).2 hx0⟩ (by
      refine ⟨∑ i, |c i| * R, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxR := hR x ((aux1_matFeas A b x).1 hx)
      rw [aux1_dotL_apply, dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      calc c i * x i ≤ |c i * x i| := le_abs_self _
        _ = |c i| * |x i| := abs_mul _ _
        _ ≤ |c i| * R := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at this
          linarith)
  exact ⟨yz.1, (aux1_matDual A c yz).1 hyz⟩

-- K2-aux: functionals on `n → ℝ` are dot products
theorem Module.Dual.exists_dotProduct_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (n → ℝ)) : ∃ u : n → ℝ, ∀ v, φ v = u ⬝ᵥ v := by
  refine ⟨fun i => φ (Pi.single i 1), fun v => ?_⟩
  rw [aux1_linear_pi φ v, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

-- K2-aux: functionals on matrices are trace pairings
theorem Module.Dual.exists_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (Matrix n n ℝ)) : ∃ Y : Matrix n n ℝ, ∀ A, φ A = (Yᵀ * A).trace := by
  refine ⟨Matrix.of fun i j => φ (Matrix.single i j 1), fun A => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  have hs : ∀ i j, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
    intro i j; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [map_sum, hs, map_smul, smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end DualityKit

namespace DualityKit

open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma aux2_interior_nonempty {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]
    {s : Set W} (hs : Convex ℝ s) (h : affineSpan ℝ s = ⊤) : (interior s).Nonempty := by
  let e : W ≃L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) :=
    (Module.finBasis ℝ W).equivFun.toContinuousLinearEquiv
  have h1 : Convex ℝ (e '' s) := hs.is_linear_image (f := ⇑e) e.toLinearMap.isLinear
  have h2 : affineSpan ℝ (e '' s) = ⊤ :=
    (AffineEquiv.span_eq_top_iff e.toLinearEquiv.toAffineEquiv).1 h
  obtain ⟨z, hz⟩ := (h1.interior_nonempty_iff_affineSpan_eq_top).2 h2
  have h3 : z ∈ e.toHomeomorph '' interior s := by
    rw [e.toHomeomorph.image_interior s]; exact hz
  obtain ⟨w, hw, -⟩ := h3
  exact ⟨w, hw⟩

private lemma aux2_lin_nonneg (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ t → b - t * a ≤ 0) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  have ht : 0 ≤ (|b| + 1) / (-a) := div_nonneg (by positivity) (by linarith)
  have := h _ ht
  have e : (|b| + 1) / (-a) * a = -(|b| + 1) := by
    rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self ha.ne, mul_one]
  rw [e] at this
  linarith [neg_abs_le b]

private lemma aux2_lim (a c μ : ℝ) (hμ : 0 < μ) (h : ∀ s : ℝ, s < c → a + s * μ ≤ 0) :
    a + c * μ ≤ 0 := by
  by_contra hc
  push Not at hc
  have hs : c - (a + c * μ) / (2 * μ) < c := by
    have : 0 < (a + c * μ) / (2 * μ) := by positivity
    linarith
  have := h _ hs
  have e : (c - (a + c * μ) / (2 * μ)) * μ = c * μ - (a + c * μ) / 2 := by field_simp
  rw [e] at this
  linarith

-- K4: Lagrange multiplier theorem, generalized Slater
theorem exists_lagrange_multiplier {X F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [T2Space F] [FiniteDimensional ℝ F]
    (S : Set X) (f : X → ℝ) (G : X → F) (K : PointedCone ℝ F)
    -- Fan convexlike: mixtures stay in `S`, improve `f`, and stay at least as feasible
    (hcvx : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x ∈ S,
        G x - (t • G x₁ + (1 - t) • G x₂) ∈ K ∧ t * f x₁ + (1 - t) * f x₂ ≤ f x)
    -- generalized Slater: perturbation domain contains a neighbourhood of 0
    -- (this covers equalities, K = ⊥, via "moment vector in the interior")
    (hslater : (0 : F) ∈ interior {u | ∃ x ∈ S, G x - u ∈ K})
    (p : ℝ) (hp : ∀ x ∈ S, G x ∈ K → f x ≤ p) :
    ∃ y : Module.Dual ℝ F, (∀ k ∈ K, 0 ≤ y k) ∧ ∀ x ∈ S, f x + y (G x) ≤ p := by
  classical
  set U : Set F := {u | ∃ x ∈ S, G x - u ∈ K} with hUdef
  have hU : U ∈ nhds (0 : F) := mem_interior_iff_mem_nhds.1 hslater
  set D : Set (F × ℝ) := {q | ∃ x ∈ S, G x - q.1 ∈ K ∧ q.2 < f x - p} with hDdef
  -- convexity of D
  have hDconv : Convex ℝ D := by
    rintro ⟨u₁, s₁⟩ ⟨x₁, hx₁, hK₁, hs₁⟩ ⟨u₂, s₂⟩ ⟨x₂, hx₂, hK₂, hs₂⟩ a b ha hb hab
    obtain ⟨x, hx, hKx, hfx⟩ := hcvx x₁ hx₁ x₂ hx₂ a ha (by linarith)
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨x, hx, ?_, ?_⟩
    · have e : G x - (a • u₁ + (1 - a) • u₂) = (G x - (a • G x₁ + (1 - a) • G x₂)) +
          (a • (G x₁ - u₁) + (1 - a) • (G x₂ - u₂)) := by
        simp only [smul_sub]; abel
      simp only [Prod.fst_add, Prod.smul_fst]
      rw [e]
      exact K.add_mem hKx (K.add_mem (PointedCone.smul_mem K ha hK₁) (PointedCone.smul_mem K hb hK₂))
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      simp only at hs₁ hs₂
      rcases ha.eq_or_lt with ha0 | ha0
      · subst ha0; linarith
      · have h1 : a * s₁ < a * (f x₁ - p) := mul_lt_mul_of_pos_left hs₁ ha0
        have h2 : (1 - a) * s₂ ≤ (1 - a) * (f x₂ - p) := mul_le_mul_of_nonneg_left hs₂.le hb
        nlinarith
  -- D is downward closed and has points over U
  have hDdown : ∀ u s s', (u, s) ∈ D → s' ≤ s → (u, s') ∈ D := by
    rintro u s s' ⟨x, hx, hK, hs⟩ hle
    exact ⟨x, hx, hK, lt_of_le_of_lt hle hs⟩
  have hDU : ∀ u ∈ U, ∃ s, (u, s) ∈ D := by
    rintro u ⟨x, hx, hK⟩
    exact ⟨f x - p - 1, x, hx, hK, by simp⟩
  -- absorbing
  have habs : ∀ v : F, ∃ c : ℝ, 0 < c ∧ c • v ∈ U ∧ (-c) • v ∈ U := by
    intro v
    have ht : Filter.Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) := by
      exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • v).tendsto' 0 0
        (zero_smul ℝ v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (ht hU)
    refine ⟨ε / 2, by positivity, hball ?_, hball ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith
  obtain ⟨s₀, hs₀⟩ := hDU 0 (mem_of_mem_nhds hU)
  -- affine span of D is everything
  have hspan : affineSpan ℝ D = ⊤ := by
    have hne : (affineSpan ℝ D : Set (F × ℝ)).Nonempty := ⟨_, subset_affineSpan ℝ D hs₀⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne, direction_affineSpan, eq_top_iff]
    rintro ⟨v, r⟩ -
    have e01 : ((0 : F), (1 : ℝ)) ∈ vectorSpan ℝ D := by
      have := vsub_mem_vectorSpan ℝ hs₀ (hDdown 0 s₀ (s₀ - 1) hs₀ (by linarith))
      simpa using this
    have hu0 : ∀ u ∈ U, ((u : F), (0 : ℝ)) ∈ vectorSpan ℝ D := by
      intro u hu
      obtain ⟨s, hs⟩ := hDU u hu
      have h1 := vsub_mem_vectorSpan ℝ hs hs₀
      have h2 := (vectorSpan ℝ D).smul_mem (s - s₀) e01
      have h3 := (vectorSpan ℝ D).sub_mem h1 h2
      convert h3 using 1
      ext <;> simp
    obtain ⟨c, hc, hcv, -⟩ := habs v
    have h3 := (vectorSpan ℝ D).smul_mem c⁻¹ (hu0 _ hcv)
    have h4 := (vectorSpan ℝ D).smul_mem r e01
    have h5 := (vectorSpan ℝ D).add_mem h3 h4
    convert h5 using 1
    ext <;> simp [smul_smul, inv_mul_cancel₀ hc.ne']
  have hint : (interior D).Nonempty := aux2_interior_nonempty hDconv hspan
  have hnot : ((0 : F), (0 : ℝ)) ∉ interior D := by
    intro h
    obtain ⟨x, hx, hK, hlt⟩ := interior_subset h
    simp only [sub_zero] at hK hlt
    linarith [hp x hx hK]
  obtain ⟨φ, hφne, hφ⟩ := geometric_hahn_banach_of_nonempty_interior_point hDconv hnot hint
  have hφ0 : φ ((0 : F), (0 : ℝ)) = 0 := by
    rw [show ((0 : F), (0 : ℝ)) = 0 from rfl, map_zero]
  set μ := φ ((0 : F), (1 : ℝ)) with hμdef
  have hdec : ∀ (u : F) (s : ℝ), φ (u, s) = φ (u, 0) + s * μ := by
    intro u s
    rw [hμdef, ← smul_eq_mul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hD' : ∀ u s, (u, s) ∈ D → φ (u, 0) + s * μ ≤ 0 := by
    intro u s h
    rw [← hdec, ← hφ0]
    exact hφ _ h
  -- μ ≥ 0
  have hμ0 : 0 ≤ μ := by
    have := aux2_lin_nonneg μ (φ (0, 0) + s₀ * μ) fun t ht => by
      have := hD' 0 (s₀ - t) (hDdown 0 s₀ _ hs₀ (by linarith))
      linarith
    exact this
  -- μ ≠ 0
  have hμpos : 0 < μ := by
    refine lt_of_le_of_ne hμ0 fun hμz => hφne ?_
    have hlam : ∀ u ∈ U, φ (u, 0) ≤ 0 := by
      intro u hu
      obtain ⟨s, hs⟩ := hDU u hu
      have := hD' u s hs
      rw [← hμz, mul_zero, add_zero] at this
      exact this
    have hzero : ∀ v : F, φ (v, 0) = 0 := by
      intro v
      obtain ⟨c, hc, h1, h2⟩ := habs v
      have e1 : φ (c • v, 0) = c * φ (v, 0) := by
        rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
      have e2 : φ ((-c) • v, 0) = -c * φ (v, 0) := by
        rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
      have a1 := hlam _ h1
      have a2 := hlam _ h2
      rw [e1] at a1
      rw [e2] at a2
      have : φ (v, 0) ≤ 0 := by
        by_contra h; push Not at h; nlinarith
      have : 0 ≤ φ (v, 0) := by
        by_contra h; push Not at h; nlinarith
      linarith
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨v, s⟩ := q
    rw [hdec, hzero, ← hμz]
    simp
  -- the multiplier
  let y : Module.Dual ℝ F := μ⁻¹ • ((φ : F × ℝ →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ F ℝ))
  have hy : ∀ u, y u = μ⁻¹ * φ (u, 0) := fun u => rfl
  refine ⟨y, fun k hk => ?_, fun x hx => ?_⟩
  · rw [hy]
    refine mul_nonneg (inv_nonneg.2 hμ0) ?_
    obtain ⟨x₀', hx₀', hK₀⟩ := (show (0 : F) ∈ U from mem_of_mem_nhds hU)
    refine aux2_lin_nonneg _ ((f x₀' - p - 1) * μ) fun t ht => ?_
    have hmem : ((-t) • k, f x₀' - p - 1) ∈ D := by
      refine ⟨x₀', hx₀', ?_, by simp⟩
      have : G x₀' - (-t) • k = (G x₀' - 0) + t • k := by simp [neg_smul]
      rw [this]
      exact K.add_mem hK₀ (PointedCone.smul_mem K ht hk)
    have := hD' _ _ hmem
    have e : φ ((-t) • k, 0) = -t * φ (k, 0) := by
      rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
    rw [e] at this
    linarith
  · have hlim := aux2_lim (φ (G x, 0)) (f x - p) μ hμpos fun s hs => hD' _ _ ⟨x, hx, by simp, hs⟩
    rw [hy]
    have : μ⁻¹ * φ (G x, 0) ≤ -(f x - p) := by
      rw [inv_mul_le_iff₀ hμpos]; linarith
    linarith

-- K5: the quadratic-form cone `{A | ∀ v, 0 ≤ v ⬝ᵥ A *ᵥ v}`
def psdForm (n : Type*) [Fintype n] : PointedCone ℝ (Matrix n n ℝ) where
  carrier := {A | ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v}
  add_mem' := by
    intro A B hA hB v
    simp only [Set.mem_ofPred_eq, Matrix.add_mulVec, dotProduct_add] at *
    exact add_nonneg (hA v) (hB v)
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro t A hA v
    have h : (0 : ℝ) ≤ (t : ℝ) * (v ⬝ᵥ A *ᵥ v) := mul_nonneg t.2 (hA v)
    simp only [Matrix.smul_mulVec, dotProduct_smul]
    exact h

private lemma aux2_mem_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} :
    A ∈ psdForm n ↔ ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v := Iff.rfl

private lemma aux2_isHermitian {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hA

private lemma aux2_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma aux2_dot_self_pos {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (aux2_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))

private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_normalize {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos := aux2_dot_self_pos hv
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, inv_pos.2 hs, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  linarith [hs2]

private def aux2_sph (n : Type*) [Fintype n] : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}

private lemma aux2_sph_compact (n : Type*) [Fintype n] : IsCompact (aux2_sph n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    have h2 : v ⬝ᵥ v = 1 := hv
    rw [Real.norm_eq_abs]
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]

private lemma aux2_sph_ne {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ∈ aux2_sph n) : v ≠ 0 := by
  rintro rfl; simp [aux2_sph] at hv

private lemma aux2_trace_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * vecMulVec x x).trace = x ⬝ᵥ M *ᵥ x := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma aux2_vecMulVec_mem {n : Type*} [Fintype n] (v : n → ℝ) : vecMulVec v v ∈ psdForm n := by
  intro w
  simpa using (posSemidef_vecMulVec_self_star v).dotProduct_mulVec_nonneg w

open scoped MatrixOrder in
private lemma aux2_trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  have hB0 : 0 ≤ B := hB.nonneg
  have hS : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB0
  have hSh : (CFC.sqrt B)ᴴ = CFC.sqrt B := hS.isHermitian.eq
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt B)).trace_nonneg
  rw [hSh] at h
  rw [← hSS, ← mul_assoc, trace_mul_cycle]
  exact h

-- K5: on symmetric matrices, psdForm is PosSemidef
theorem mem_psdForm_iff_posSemidef {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsSymm) :
    A ∈ psdForm n ↔ A.PosSemidef := by
  rw [aux2_mem_psdForm, posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h; exact ⟨aux2_isHermitian hA, fun x => by simpa using h x⟩
  · rintro ⟨-, h⟩ v; simpa using h v

-- K5: PD matrices are interior points of psdForm
theorem Matrix.PosDef.mem_interior_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A ∈ interior (psdForm n : Set (Matrix n n ℝ)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos : ∀ v ∈ aux2_sph n, 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using hA.dotProduct_mulVec_pos (aux2_sph_ne hv)
  have hcont : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.2 ⬝ᵥ z.1 *ᵥ z.2) :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hev := (aux2_sph_compact n).eventually_forall_of_forall_eventually (x₀ := A)
    (P := fun B v => 0 < v ⬝ᵥ B *ᵥ v)
    (fun v hv => hcont.continuousAt.eventually (lt_mem_nhds (hpos v hv)))
  filter_upwards [hev] with B hB
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc, hcv⟩ := aux2_normalize hv
  have h := hB _ hcv
  rw [aux2_qf_smul] at h
  exact (pos_of_mul_pos_right h (sq_nonneg c)).le

-- K5: the dual cone of psdForm is the symmetric PSD matrices
theorem psdForm_dual {n : Type*} [Fintype n] [DecidableEq n] (y : Module.Dual ℝ (Matrix n n ℝ))
    (hy : ∀ A ∈ psdForm n, 0 ≤ y A) : ∃ Y : Matrix n n ℝ, Y.PosSemidef ∧ ∀ A, y A = (Yᵀ * A).trace := by
  let Y : Matrix n n ℝ := fun i j => y (Matrix.single i j 1)
  have hrep : ∀ A, y A = (Yᵀ * A).trace := by
    intro A
    conv_lhs => rw [matrix_eq_sum_single A]
    have hs : ∀ i j, y (Matrix.single i j (A i j)) = A i j * Y i j := by
      intro i j
      have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
        rw [smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
    simp only [map_sum, hs, trace, diag, mul_apply, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hanti : ∀ i j, Matrix.single i j (1 : ℝ) - Matrix.single j i 1 ∈ psdForm n := by
    intro i j v
    have : v ⬝ᵥ (Matrix.single i j (1 : ℝ) - Matrix.single j i 1) *ᵥ v = 0 := by
      simp only [sub_mulVec, dotProduct_sub, single_mulVec, one_mul]
      change v ⬝ᵥ Pi.single i (v j) - v ⬝ᵥ Pi.single j (v i) = 0
      simp only [dotProduct_single]
      ring
    rw [this]
  have hsymm : Yᵀ = Y := by
    ext i j
    have h1 := hy _ (hanti i j)
    have h2 := hy _ (hanti j i)
    simp only [map_sub] at h1 h2
    show y (Matrix.single j i 1) = y (Matrix.single i j 1)
    linarith
  refine ⟨Y, ?_, hrep⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact aux2_isHermitian hsymm
  · have h := hy _ (aux2_vecMulVec_mem x)
    rw [hrep, aux2_trace_vecMulVec, hsymm] at h
    simpa using h

-- K5: trace pairing of PSD matrices is nonnegative
theorem Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := aux2_trace_mul_nonneg hA hB

-- K5: self-duality of the PSD cone (symmetric matrices)
theorem Matrix.posSemidef_iff_forall_trace_mul_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsSymm) :
    A.PosSemidef ↔ ∀ B : Matrix n n ℝ, B.PosSemidef → 0 ≤ (A * B).trace := by
  refine ⟨fun h B hB => aux2_trace_mul_nonneg h hB, fun h => ?_⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg (aux2_isHermitian hA) fun x => ?_
  have := h (vecMulVec x x) (by simpa using posSemidef_vecMulVec_self_star x)
  rw [aux2_trace_vecMulVec] at this
  simpa using this

-- K5: the PSD set is closed
theorem Matrix.isClosed_setOf_posSemidef {n : Type*} [Fintype n] : IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by
  have : {A : Matrix n n ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : n → ℝ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A; simp only [Set.mem_ofPred_eq, posSemidef_iff_dotProduct_mulVec, IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

private lemma aux2_roots (bx by' kb : ℝ) (hx : 0 < bx) (hy : by' < 0) :
    ∃ s₁ s₂ : ℝ, s₁ < 0 ∧ 0 < s₂ ∧ bx + s₁ * kb + s₁ ^ 2 * by' = 0 ∧
      bx + s₂ * kb + s₂ ^ 2 * by' = 0 := by
  have hD : 0 ≤ kb ^ 2 - 4 * bx * by' := by nlinarith
  set r := Real.sqrt (kb ^ 2 - 4 * bx * by') with hr_def
  have hr2 : r ^ 2 = kb ^ 2 - 4 * bx * by' := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrk1 : kb < r := by nlinarith
  have hrk2 : -kb < r := by nlinarith
  have hy2 : (2 * by') ≠ 0 := by linarith
  have hy4 : (4 * by') ≠ 0 := by linarith
  refine ⟨(-kb + r) / (2 * by'), (-kb - r) / (2 * by'), ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · set s := (-kb + r) / (2 * by')
    have hs : 2 * by' * s = -kb + r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb + r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h
  · set s := (-kb - r) / (2 * by')
    have hs : 2 * by' * s = -kb - r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb - r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h

private lemma aux2_pair_real (ax bx ay by' ka kb s₁ s₂ : ℝ) (hx : 0 < bx) (hs₁ : s₁ < 0) (hs₂ : 0 < s₂)
    (hb₁ : bx + s₁ * kb + s₁ ^ 2 * by' = 0) (hb₂ : bx + s₂ * kb + s₂ ^ 2 * by' = 0)
    (ha₁ : 0 ≤ ax + s₁ * ka + s₁ ^ 2 * ay) (ha₂ : 0 ≤ ax + s₂ * ka + s₂ ^ 2 * ay) :
    0 ≤ ay * bx - ax * by' := by
  by_contra hC
  push Not at hC
  set C := ay * bx - ax * by'
  set γ := ka * bx - ax * kb
  -- h(s) = (a-part)·bx - ax·(b-part) = s γ + s² C
  have e₁ : (ax + s₁ * ka + s₁ ^ 2 * ay) * bx - ax * (bx + s₁ * kb + s₁ ^ 2 * by') =
      s₁ * (γ + s₁ * C) := by simp only [γ, C]; ring
  have e₂ : (ax + s₂ * ka + s₂ ^ 2 * ay) * bx - ax * (bx + s₂ * kb + s₂ ^ 2 * by') =
      s₂ * (γ + s₂ * C) := by simp only [γ, C]; ring
  rw [hb₁, mul_zero, sub_zero] at e₁
  rw [hb₂, mul_zero, sub_zero] at e₂
  have h₁ : 0 ≤ s₁ * (γ + s₁ * C) := e₁ ▸ mul_nonneg ha₁ hx.le
  have h₂ : 0 ≤ s₂ * (γ + s₂ * C) := e₂ ▸ mul_nonneg ha₂ hx.le
  have h₁' : γ + s₁ * C ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h₂' : 0 ≤ γ + s₂ * C := by
    by_contra h; push Not at h; nlinarith
  nlinarith

private lemma aux2_core {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V → ℝ)
    (ha : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, a (x + s • y) = a x + s * k + s ^ 2 * a y)
    (hb : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, b (x + s • y) = b x + s * k + s ^ 2 * b y)
    (hslater : ∃ x₀, 0 < b x₀) (H : ∀ x, 0 ≤ b x → 0 ≤ a x) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ a x - τ * b x := by
  -- pair inequality
  have hpair : ∀ x y, 0 < b x → b y < 0 → 0 ≤ a y * b x - a x * b y := by
    intro x y hx hy
    obtain ⟨ka, hka⟩ := ha x y
    obtain ⟨kb, hkb⟩ := hb x y
    obtain ⟨s₁, s₂, hs₁, hs₂, h₁, h₂⟩ := aux2_roots (b x) (b y) kb hx hy
    refine aux2_pair_real (a x) (b x) (a y) (b y) ka kb s₁ s₂ hx hs₁ hs₂ h₁ h₂ ?_ ?_
    · rw [← hka]; exact H _ (by rw [hkb, h₁])
    · rw [← hka]; exact H _ (by rw [hkb, h₂])
  obtain ⟨x₀, hx₀⟩ := hslater
  let S : Set ℝ := {q | ∃ x, 0 < b x ∧ q = a x / b x}
  have hSne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hS0 : ∀ q ∈ S, 0 ≤ q := by
    rintro q ⟨x, hx, rfl⟩; exact div_nonneg (H x hx.le) hx.le
  have hSbdd : BddBelow S := ⟨0, hS0⟩
  refine ⟨sInf S, le_csInf hSne hS0, fun x => ?_⟩
  rcases lt_trichotomy (b x) 0 with hneg | hzero | hpos
  · have hle : a x / b x ≤ sInf S := by
      refine le_csInf hSne ?_
      rintro q ⟨z, hz, rfl⟩
      rw [div_le_iff_of_neg hneg, div_mul_eq_mul_div, div_le_iff₀ hz]
      linarith [hpair z x hz hneg]
    rw [div_le_iff_of_neg hneg] at hle
    linarith
  · rw [hzero, mul_zero, sub_zero]; exact H x hzero.ge
  · have hle : sInf S ≤ a x / b x := csInf_le hSbdd ⟨x, hpos, rfl⟩
    rw [le_div_iff₀ hpos] at hle
    linarith

private lemma aux2_qexp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ A *ᵥ (x + s • y) =
      x ⬝ᵥ A *ᵥ x + s * (x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ x) + s ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_qf_sub_smul {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (τ : ℝ) (x : n → ℝ) :
    x ⬝ᵥ (A - τ • B) *ᵥ x = x ⬝ᵥ A *ᵥ x - τ * (x ⬝ᵥ B *ᵥ x) := by
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma aux2_symm_sub_smul {n : Type*} {A B : Matrix n n ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (τ : ℝ) : (A - τ • B).IsSymm := by
  unfold IsSymm at *
  rw [transpose_sub, transpose_smul, hA, hB]

-- K6: S-lemma (Yakubovich), Slater form
theorem Matrix.sLemma {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hslater : ∃ x₀, 0 < x₀ ⬝ᵥ B *ᵥ x₀) :
    (∀ x, 0 ≤ x ⬝ᵥ B *ᵥ x → 0 ≤ x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosSemidef := by
  constructor
  · intro H
    obtain ⟨τ, hτ, h⟩ := aux2_core (fun x => x ⬝ᵥ A *ᵥ x) (fun x => x ⬝ᵥ B *ᵥ x)
      (fun x y => ⟨_, aux2_qexp A x y⟩) (fun x y => ⟨_, aux2_qexp B x y⟩) hslater H
    refine ⟨τ, hτ, PosSemidef.of_dotProduct_mulVec_nonneg
      (aux2_isHermitian (aux2_symm_sub_smul hA hB τ)) fun x => ?_⟩
    simpa [aux2_qf_sub_smul] using h x
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h.dotProduct_mulVec_nonneg x
    simp only [star_trivial, aux2_qf_sub_smul] at this
    nlinarith

-- K6: strict S-lemma (Finsler–Yakubovich), no Slater needed
/-- Strict form (Finsler–Yakubovich). True without Slater (checked on paper, see STATEMENTS.md):
with a Slater point it follows from `sLemma` applied to `A - ε • 1`; without one, `-B` is PSD and
it is Finsler's lemma. -/
theorem Matrix.sLemma_strict {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) :
    (∀ x, x ≠ 0 → 0 ≤ x ⬝ᵥ B *ᵥ x → 0 < x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosDef := by
  classical
  have hcA : Continuous fun x : n → ℝ => x ⬝ᵥ A *ᵥ x :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hcB : Continuous fun x : n → ℝ => x ⬝ᵥ B *ᵥ x :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  constructor
  · intro H
    by_cases hsl : ∃ x₀, 0 < x₀ ⬝ᵥ B *ᵥ x₀
    · -- Slater case: uniform ε on the compact set {‖x‖ = 1, b x ≥ 0}
      let K' : Set (n → ℝ) := aux2_sph n ∩ {x | 0 ≤ x ⬝ᵥ B *ᵥ x}
      have hK' : IsCompact K' :=
        (aux2_sph_compact n).inter_right (isClosed_le continuous_const hcB)
      obtain ⟨m, hm⟩ := hK'.elim_directed_cover
        (fun m : ℕ => {x : n → ℝ | 1 / ((m : ℝ) + 1) < x ⬝ᵥ A *ᵥ x})
        (fun m => isOpen_lt continuous_const hcA)
        (fun x hx => by
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (H x (aux2_sph_ne hx.1) hx.2)
          exact Set.mem_iUnion.2 ⟨m, hm⟩)
        (Monotone.directed_le fun i j hij x hx => by
          refine lt_of_le_of_lt ?_ (show 1 / ((i : ℝ) + 1) < _ from hx)
          gcongr)
      set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
      have hε0 : 0 < ε := by positivity
      have hI : (A - ε • (1 : Matrix n n ℝ)).IsSymm := by
        unfold IsSymm at *; rw [transpose_sub, transpose_smul, transpose_one, hA]
      have hq : ∀ x, 0 ≤ x ⬝ᵥ B *ᵥ x → 0 ≤ x ⬝ᵥ (A - ε • (1 : Matrix n n ℝ)) *ᵥ x := by
        intro x hx
        rw [aux2_qf_sub_smul, one_mulVec]
        by_cases hx0 : x = 0
        · simp [hx0]
        obtain ⟨c, hc, hcx⟩ := aux2_normalize hx0
        have hmem : c • x ∈ K' := ⟨hcx, show 0 ≤ (c • x) ⬝ᵥ B *ᵥ (c • x) by rw [aux2_qf_smul]; positivity⟩
        have h1 := hm hmem
        simp only [Set.mem_ofPred_eq, aux2_qf_smul] at h1
        simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hcx
        nlinarith
      obtain ⟨τ, hτ, hpsd⟩ := (Matrix.sLemma hI hB hsl).1 hq
      refine ⟨τ, hτ, PosDef.of_dotProduct_mulVec_pos
        (aux2_isHermitian (aux2_symm_sub_smul hA hB τ)) fun x hx => ?_⟩
      have h1 := hpsd.dotProduct_mulVec_nonneg x
      have h2 := aux2_dot_self_pos hx
      simp only [star_trivial, aux2_qf_sub_smul, one_mulVec] at h1 ⊢
      nlinarith
    · -- no Slater: b ≤ 0 everywhere, Finsler by a directed compact cover
      push Not at hsl
      obtain ⟨k, hk⟩ := (aux2_sph_compact n).elim_directed_cover
        (fun k : ℕ => {x : n → ℝ | 0 < x ⬝ᵥ A *ᵥ x - (k : ℝ) * (x ⬝ᵥ B *ᵥ x)})
        (fun k => isOpen_lt continuous_const (hcA.sub (continuous_const.mul hcB)))
        (fun x hx => by
          rcases (hsl x).lt_or_eq with hlt | heq
          · obtain ⟨k, hk⟩ := exists_nat_gt ((-(x ⬝ᵥ A *ᵥ x)) / (-(x ⬝ᵥ B *ᵥ x)))
            refine Set.mem_iUnion.2 ⟨k, ?_⟩
            have hnb : 0 < -(x ⬝ᵥ B *ᵥ x) := by linarith
            rw [div_lt_iff₀ hnb] at hk
            simp only [Set.mem_ofPred_eq]
            linarith
          · refine Set.mem_iUnion.2 ⟨0, ?_⟩
            simp only [Set.mem_ofPred_eq, Nat.cast_zero, zero_mul, sub_zero]
            exact H x (aux2_sph_ne hx) heq.ge)
        (Monotone.directed_le fun i j hij x hx => by
          have hx' : 0 < x ⬝ᵥ A *ᵥ x - (i : ℝ) * (x ⬝ᵥ B *ᵥ x) := hx
          show 0 < x ⬝ᵥ A *ᵥ x - (j : ℝ) * (x ⬝ᵥ B *ᵥ x)
          have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
          nlinarith [hsl x])
      refine ⟨k, by positivity, PosDef.of_dotProduct_mulVec_pos
        (aux2_isHermitian (aux2_symm_sub_smul hA hB _)) fun x hx => ?_⟩
      obtain ⟨c, hc, hcx⟩ := aux2_normalize hx
      have h1 := hk hcx
      simp only [Set.mem_ofPred_eq, aux2_qf_smul] at h1
      simp only [star_trivial, aux2_qf_sub_smul]
      have hc2 : 0 < c ^ 2 := by positivity
      nlinarith
  · rintro ⟨τ, hτ, h⟩ x hx0 hx
    have := h.dotProduct_mulVec_pos hx0
    simp only [star_trivial, aux2_qf_sub_smul] at this
    nlinarith

private def aux2_Q {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p : (n → ℝ) × ℝ) : ℝ :=
  p.1 ⬝ᵥ A *ᵥ p.1 + 2 * p.2 * (b ⬝ᵥ p.1) + c * p.2 ^ 2

private lemma aux2_Q_exp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p q : (n → ℝ) × ℝ) (s : ℝ) :
    aux2_Q A b c (p + s • q) = aux2_Q A b c p + s * (p.1 ⬝ᵥ A *ᵥ q.1 + q.1 ⬝ᵥ A *ᵥ p.1 +
      2 * (p.2 * (b ⬝ᵥ q.1) + q.2 * (b ⬝ᵥ p.1)) + 2 * c * p.2 * q.2) + s ^ 2 * aux2_Q A b c q := by
  simp only [aux2_Q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [aux2_qexp]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_Q_one {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ) (x : n → ℝ) :
    aux2_Q A b c (x, 1) = x ⬝ᵥ A *ᵥ x + 2 * b ⬝ᵥ x + c := by
  simp only [aux2_Q]; ring

private lemma aux2_Q_scale {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (u : n → ℝ) (t : ℝ) : aux2_Q A b c (t • u, t) = t ^ 2 * aux2_Q A b c (u, 1) := by
  simp only [aux2_Q, aux2_qf_smul, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_big (f₀ k q : ℝ) (hq : q < 0) : ∃ S : ℝ, 0 ≤ S ∧ f₀ + S * k + S ^ 2 * q < 0 := by
  set M := |f₀| + |k| + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M / (-q) + 1, ?_⟩
  set S := M / (-q) + 1 with hS
  have hS1 : 1 ≤ S := by have : 0 ≤ M / (-q) := div_nonneg hM0.le (by linarith); linarith
  have hSq : S * q = -M + q := by
    rw [hS, add_mul, div_mul_eq_mul_div, one_mul]
    rw [div_neg, mul_div_assoc, div_self hq.ne, mul_one]
  have h1 : f₀ ≤ S * |f₀| := by nlinarith [le_abs_self f₀, abs_nonneg f₀]
  have h2 : S * k ≤ S * |k| := by nlinarith [le_abs_self k]
  have h3 : S ^ 2 * q = S * (-M + q) := by rw [← hSq]; ring
  refine ⟨by linarith, ?_⟩
  nlinarith

private lemma aux2_t0 {V : Type*} [AddCommGroup V] [Module ℝ V] (Q₁ Q₂ : V → ℝ) (P d : V)
    (h1 : ∃ k, ∀ s : ℝ, Q₁ (P + s • d) = Q₁ P + s * k + s ^ 2 * Q₁ d)
    (h2 : ∃ k, ∀ s : ℝ, Q₂ (P + s • d) = Q₂ P + s * k + s ^ 2 * Q₂ d)
    (hP : Q₂ P < 0) (hd : Q₂ d ≤ 0) (H : ∀ s : ℝ, Q₂ (P + s • d) ≤ 0 → 0 ≤ Q₁ (P + s • d)) :
    0 ≤ Q₁ d := by
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  by_contra hneg
  push Not at hneg
  have key : ∀ s : ℝ, s * k₂ ≤ 0 → 0 ≤ Q₁ P + s * k₁ + s ^ 2 * Q₁ d := by
    intro s hs
    rw [← hk₁]
    apply H
    rw [hk₂]
    nlinarith [sq_nonneg s]
  rcases le_total k₂ 0 with hk | hk
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) k₁ (Q₁ d) hneg
    linarith [key S (mul_nonpos_of_nonneg_of_nonpos hS0 hk)]
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) (-k₁) (Q₁ d) hneg
    have := key (-S) (by nlinarith)
    nlinarith

-- K6: inhomogeneous S-lemma
/-- Inhomogeneous form (quadratic functions), Slater `g x₀ < 0`. -/
theorem sLemma_inhom {n : Type*} [Fintype n] (A₁ A₂ : Matrix n n ℝ) (b₁ b₂ : n → ℝ) (c₁ c₂ : ℝ)
    (hslater : ∃ x₀, x₀ ⬝ᵥ A₂ *ᵥ x₀ + 2 * b₂ ⬝ᵥ x₀ + c₂ < 0) :
    (∀ x, x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂ ≤ 0 → 0 ≤ x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ (x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) + τ * (x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂) := by
  constructor
  · intro H
    obtain ⟨x₀, hx₀⟩ := hslater
    have H1 : ∀ u, aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 → 0 ≤ aux2_Q A₁ b₁ c₁ (u, 1) := by
      intro u hu
      rw [aux2_Q_one] at hu ⊢
      exact H u hu
    have hP0 : aux2_Q A₂ b₂ c₂ (x₀, 1) < 0 := by rw [aux2_Q_one]; exact hx₀
    have hHom : ∀ p : (n → ℝ) × ℝ, 0 ≤ -aux2_Q A₂ b₂ c₂ p → 0 ≤ aux2_Q A₁ b₁ c₁ p := by
      rintro ⟨w, t⟩ hp
      by_cases ht : t = 0
      · subst ht
        have hline : ∀ s : ℝ, ((x₀, (1 : ℝ)) + s • (w, (0 : ℝ))) = (x₀ + s • w, 1) := by
          intro s; ext <;> simp
        refine aux2_t0 (aux2_Q A₁ b₁ c₁) (aux2_Q A₂ b₂ c₂) (x₀, 1) (w, 0)
          ⟨_, aux2_Q_exp A₁ b₁ c₁ (x₀, 1) (w, 0)⟩ ⟨_, aux2_Q_exp A₂ b₂ c₂ (x₀, 1) (w, 0)⟩
          hP0 (by linarith) fun s hs => ?_
        rw [hline] at hs ⊢
        exact H1 _ hs
      · obtain ⟨u, rfl⟩ : ∃ u, w = t • u := ⟨t⁻¹ • w, by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]⟩
        rw [aux2_Q_scale] at hp ⊢
        have ht2 : 0 < t ^ 2 := by positivity
        have h2 : aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 := by nlinarith
        have := H1 u h2
        positivity
    obtain ⟨τ, hτ, h⟩ := aux2_core (aux2_Q A₁ b₁ c₁) (fun p => -aux2_Q A₂ b₂ c₂ p)
      (fun p q => ⟨_, aux2_Q_exp A₁ b₁ c₁ p q⟩)
      (fun p q => ⟨-(p.1 ⬝ᵥ A₂ *ᵥ q.1 + q.1 ⬝ᵥ A₂ *ᵥ p.1 +
          2 * (p.2 * (b₂ ⬝ᵥ q.1) + q.2 * (b₂ ⬝ᵥ p.1)) + 2 * c₂ * p.2 * q.2), fun s => by
        show -aux2_Q A₂ b₂ c₂ (p + s • q) = _
        rw [aux2_Q_exp A₂ b₂ c₂ p q s]
        ring⟩)
      ⟨(x₀, 1), by linarith⟩ hHom
    refine ⟨τ, hτ, fun x => ?_⟩
    have := h (x, 1)
    rw [aux2_Q_one, aux2_Q_one] at this
    linarith
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h x
    nlinarith

end DualityKit

namespace RRAux_QuadMatIneq_Petersen_proposition_4_16

open Matrix

section
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma herm_of_transpose {M : Matrix a a ℝ} (h : Mᵀ = M) : M.IsHermitian := by
  unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact h

lemma transpose_of_herm {M : Matrix a a ℝ} (h : M.IsHermitian) : Mᵀ = M := by
  have := h.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma dot_mulVec_eq (E : Matrix a b ℝ) (x : a → ℝ) (w : b → ℝ) :
    x ⬝ᵥ E *ᵥ w = (Eᵀ *ᵥ x) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma qf_transpose (M : Matrix a a ℝ) (x : a → ℝ) : x ⬝ᵥ Mᵀ *ᵥ x = x ⬝ᵥ M *ᵥ x := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

lemma qf_mul_transpose (E : Matrix a b ℝ) (x : a → ℝ) :
    x ⬝ᵥ (E * Eᵀ) *ᵥ x = (Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x) := by
  rw [← mulVec_mulVec, dot_mulVec_eq]

lemma qf_conj (F : Matrix b b ℝ) (G : Matrix b a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (Gᵀ * F * G) *ᵥ x = (G *ᵥ x) ⬝ᵥ F *ᵥ (G *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_eq, transpose_transpose]

lemma qf_transpose_mul (F : Matrix b a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (Fᵀ * F) *ᵥ x = (F *ᵥ x) ⬝ᵥ (F *ᵥ x) := by
  rw [← mulVec_mulVec, dot_mulVec_eq, transpose_transpose]

lemma qf_EFG (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (E * F * G) *ᵥ x = (Eᵀ *ᵥ x) ⬝ᵥ (F *ᵥ (G *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_eq]

lemma qf_blocks (P : Matrix a a ℝ) (Q : Matrix a b ℝ) (R : Matrix b b ℝ) (x : a → ℝ)
    (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ fromBlocks P Q Qᵀ R *ᵥ Sum.elim x w =
      x ⬝ᵥ P *ᵥ x + 2 * ((Qᵀ *ᵥ x) ⬝ᵥ w) + w ⬝ᵥ R *ᵥ w := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim, dotProduct_add]
  rw [dot_mulVec_eq Q x w, dotProduct_comm w (Qᵀ *ᵥ x)]
  ring


lemma dot_self_nonneg (v : a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

end

-- scalar helpers
lemma scal_cs (t α β γ ω : ℝ) (htα : t * α = β) (hω : ω ≤ α)
    (h : 0 ≤ γ - 2 * t * β + t ^ 2 * α) : 0 ≤ γ - t ^ 2 * ω := by
  subst htα
  nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg t)]

lemma scal_rev (l α β γ κ c : ℝ) (hl : 0 < l) (h1 : 0 ≤ l ^ 2 * α - 2 * l * γ + β)
    (h2 : β ≤ κ) : -c - l * α - l⁻¹ * κ ≤ -c - 2 * γ := by
  have h3 : 0 ≤ l⁻¹ * (l ^ 2 * α - 2 * l * γ + β) := mul_nonneg (inv_nonneg.mpr hl.le) h1
  have e : l⁻¹ * (l ^ 2 * α - 2 * l * γ + β) = l * α - 2 * γ + l⁻¹ * β := by
    field_simp
  have h4 : l⁻¹ * β ≤ l⁻¹ * κ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hl.le)
  linarith

lemma scal_fwd (τ c s k : ℝ) (hτ : 0 < τ) :
    (-c - 2 * (τ⁻¹ * s)) - τ * (k - τ⁻¹ * (τ⁻¹ * s)) = -c - τ⁻¹ * s - τ * k := by
  field_simp
  ring

lemma scal_zero (c d : ℝ) (hd : 0 ≤ d) (h : ∀ t : ℝ, 0 ≤ -(t * t * c) - 2 * (t * d)) : d = 0 := by
  by_contra hne
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
  set s := |c| + 1 with hs
  have hspos : 0 < s := by positivity
  set t := d / s with ht
  have htpos : 0 < t := div_pos hdpos hspos
  have hts : t * s = d := by rw [ht]; field_simp
  have h1 := h t
  rw [← hts] at h1
  have hcs : 0 < c + 2 * s := by rw [hs]; linarith [neg_abs_le c, abs_nonneg c]
  have : 0 < t * t * (c + 2 * s) := mul_pos (mul_pos htpos htpos) hcs
  linarith

lemma vecMulVec_mulVec' {p q : Type*} [Fintype q] (w : p → ℝ) (v u : q → ℝ) :
    vecMulVec w v *ᵥ u = (v ⬝ᵥ u) • w := by
  ext i; simp [mulVec, dotProduct, vecMulVec, mul_assoc]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)

lemma exists_F {p q : Type*} [Fintype p] [Fintype q] (Fbar : Matrix q q ℝ)
    (hF : Fbar.PosSemidef) (u : q → ℝ) (w : p → ℝ) (h : w ⬝ᵥ w ≤ u ⬝ᵥ Fbar *ᵥ u) :
    ∃ F : Matrix p q ℝ, (Fbar - Fᵀ * F).PosSemidef ∧ F *ᵥ u = w := by
  have hsym : Fbarᵀ = Fbar := transpose_of_herm hF.1
  have hnn : ∀ z : q → ℝ, 0 ≤ z ⬝ᵥ Fbar *ᵥ z := fun z => by
    simpa using hF.dotProduct_mulVec_nonneg z
  have hcomm : ∀ z y : q → ℝ, z ⬝ᵥ Fbar *ᵥ y = y ⬝ᵥ Fbar *ᵥ z := fun z y => by
    rw [dot_mulVec_eq, hsym, dotProduct_comm]
  set α := u ⬝ᵥ Fbar *ᵥ u with hα
  rcases (hnn u).eq_or_lt with h0 | hpos
  · have hw : w = 0 := by
      apply dotProduct_self_eq_zero.mp
      exact le_antisymm (by linarith) (dot_self_nonneg w)
    refine ⟨0, ?_, ?_⟩
    · simpa using hF
    · simp [hw]
  · refine ⟨α⁻¹ • vecMulVec w (Fbar *ᵥ u), ?_, ?_⟩
    · rw [posSemidef_iff_dotProduct_mulVec]
      refine ⟨herm_of_transpose ?_, fun z => ?_⟩
      · rw [transpose_sub, transpose_mul, transpose_transpose, hsym]
      · rw [star_trivial, sub_mulVec, dotProduct_sub, qf_transpose_mul, smul_mulVec,
          vecMulVec_mulVec', smul_smul]
        simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
        set β := (Fbar *ᵥ u) ⬝ᵥ z
        have hcs := hnn (z - (α⁻¹ * β) • u)
        rw [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
          smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul, smul_eq_mul] at hcs
        have e1 : z ⬝ᵥ Fbar *ᵥ u = β := by rw [dotProduct_comm]
        have e2 : u ⬝ᵥ Fbar *ᵥ z = β := by rw [hcomm, e1]
        rw [e1, e2, ← hα] at hcs
        simp only [smul_eq_mul] at hcs
        have := scal_cs (α⁻¹ * β) α β (z ⬝ᵥ Fbar *ᵥ z) (w ⬝ᵥ w)
          (by rw [mul_assoc, mul_comm β, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]) h
          (by linarith)
        linarith [this, show (α⁻¹ * β) ^ 2 * w ⬝ᵥ w = α⁻¹ * β * (α⁻¹ * β * w ⬝ᵥ w) by ring]
    · rw [smul_mulVec, vecMulVec_mulVec', smul_smul, dotProduct_comm, ← hcomm, ← hα,
        inv_mul_cancel₀ hpos.ne', one_smul]

lemma isSymm_blocks {a b : Type*} (P : Matrix a a ℝ) (Q : Matrix a b ℝ) (R : Matrix b b ℝ)
    (hP : Pᵀ = P) (hR : Rᵀ = R) : (fromBlocks P Q Qᵀ R).IsSymm := by
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose, hP, hR, transpose_transpose]

lemma sLemma_strict_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ y : ι → ℝ, y ≠ 0 → 0 ≤ y ⬝ᵥ B *ᵥ y → 0 < y ⬝ᵥ A *ᵥ y) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ y : ι → ℝ, y ≠ 0 → 0 < y ⬝ᵥ A *ᵥ y - τ * (y ⬝ᵥ B *ᵥ y) := by
  let A' : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks A 0 (0 : Matrix ι Unit ℝ)ᵀ 0
  let B' : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks B 0 (0 : Matrix ι Unit ℝ)ᵀ (-1)
  have qA' : ∀ y s, Sum.elim y s ⬝ᵥ A' *ᵥ Sum.elim y s = y ⬝ᵥ A *ᵥ y := fun y s => by
    rw [show A' = fromBlocks A 0 (0 : Matrix ι Unit ℝ)ᵀ 0 from rfl, qf_blocks]
    simp only [transpose_transpose, transpose_zero, zero_mulVec, zero_dotProduct,
      mul_zero, add_zero, dotProduct_zero]
  have qB' : ∀ y s, Sum.elim y s ⬝ᵥ B' *ᵥ Sum.elim y s = y ⬝ᵥ B *ᵥ y - s ⬝ᵥ s := fun y s => by
    rw [show B' = fromBlocks B 0 (0 : Matrix ι Unit ℝ)ᵀ (-1) from rfl, qf_blocks]
    simp only [transpose_transpose, transpose_zero, zero_mulVec, zero_dotProduct,
      mul_zero, add_zero, neg_mulVec, one_mulVec, dotProduct_neg]; ring
  have hA' : A'.IsSymm := isSymm_blocks _ _ _ hA.eq (by simp)
  have hB' : B'.IsSymm := isSymm_blocks _ _ _ hB.eq (by simp)
  have hcond : ∀ z : ι ⊕ Unit → ℝ, z ≠ 0 → 0 ≤ z ⬝ᵥ B' *ᵥ z → 0 < z ⬝ᵥ A' *ᵥ z := by
    intro z hz hBz
    rw [← Sum.elim_comp_inl_inr z] at hz hBz ⊢
    rw [qB'] at hBz
    rw [qA']
    by_cases hy : z ∘ Sum.inl = 0
    · exfalso
      rw [hy] at hBz hz
      simp only [zero_dotProduct] at hBz
      have hs : z ∘ Sum.inr = 0 :=
        dotProduct_self_eq_zero.mp (le_antisymm (by linarith) (dot_self_nonneg _))
      rw [hs] at hz
      exact hz (by simp)
    · exact h _ hy (by linarith [dot_self_nonneg (z ∘ Sum.inr)])
  obtain ⟨τ, -, hPD⟩ := (DualityKit.Matrix.sLemma_strict hA' hB').mp hcond
  have hτ : 0 < τ := by
    have := hPD.diag_pos (i := Sum.inr ())
    simpa [A', B'] using this
  refine ⟨τ, hτ, fun y hy => ?_⟩
  have hz : (Sum.elim y (0 : Unit → ℝ)) ≠ 0 := by
    intro h0; apply hy; have := congrArg (fun z => z ∘ Sum.inl) h0; simpa using this
  have := (posDef_iff_dotProduct_mulVec.mp hPD).2 hz
  rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, qA', qB',
    smul_eq_mul] at this
  simpa using this

section Main
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

/-- `[-C -E; -Eᵀ 0]`. -/
def MA (C : Matrix a a ℝ) (E : Matrix a b ℝ) : Matrix (a ⊕ b) (a ⊕ b) ℝ :=
  fromBlocks (-C) (-E) (-E)ᵀ 0

/-- `[GᵀF̄G 0; 0 -I]`. -/
def MB (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) : Matrix (a ⊕ b) (a ⊕ b) ℝ :=
  fromBlocks (Gᵀ * Fbar * G) 0 (0 : Matrix a b ℝ)ᵀ (-1)

omit [DecidableEq b] in
lemma qA (C : Matrix a a ℝ) (E : Matrix a b ℝ) (x : a → ℝ) (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ MA C E *ᵥ Sum.elim x w = -(x ⬝ᵥ C *ᵥ x) - 2 * ((Eᵀ *ᵥ x) ⬝ᵥ w) := by
  rw [MA, qf_blocks]
  simp only [neg_mulVec, dotProduct_neg, transpose_neg, zero_mulVec, dotProduct_zero, add_zero,
    neg_dotProduct]
  ring

lemma qB (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) (x : a → ℝ) (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ MB Fbar G *ᵥ Sum.elim x w = (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) - w ⬝ᵥ w := by
  rw [MB, qf_blocks, qf_conj]
  simp only [transpose_zero, zero_mulVec, zero_dotProduct, mul_zero, add_zero, neg_mulVec,
    one_mulVec, dotProduct_neg]
  ring

omit [DecidableEq b] in
lemma MA_symm (C : Matrix a a ℝ) (E : Matrix a b ℝ) (hC : C.IsHermitian) : (MA C E).IsSymm :=
  isSymm_blocks _ _ _ (by rw [transpose_neg, transpose_of_herm hC]) (by simp)

lemma MB_symm (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) (hF : Fbar.IsHermitian) :
    (MB (b := b) Fbar G).IsSymm :=
  isSymm_blocks _ _ _ (by rw [transpose_mul, transpose_mul, transpose_transpose,
    transpose_of_herm hF, Matrix.mul_assoc]) (by simp)

omit [DecidableEq b] in
lemma qf_target (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (lam : ℝ) (x : a → ℝ) :
    x ⬝ᵥ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))) *ᵥ x =
      -(x ⬝ᵥ C *ᵥ x) - lam * ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x)) -
        lam⁻¹ * ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) := by
  rw [neg_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    qf_mul_transpose, qf_conj]
  ring

omit [DecidableEq b] in
lemma qf_unc (C : Matrix a a ℝ) (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ)
    (x : a → ℝ) :
    x ⬝ᵥ (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)) *ᵥ x =
      -(x ⬝ᵥ C *ᵥ x) - 2 * ((Eᵀ *ᵥ x) ⬝ᵥ (F *ᵥ (G *ᵥ x))) := by
  have ht : Gᵀ * Fᵀ * Eᵀ = (E * F * G)ᵀ := by rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
  rw [ht, neg_mulVec, add_mulVec, add_mulVec, dotProduct_neg, dotProduct_add, dotProduct_add,
    qf_transpose, qf_EFG]
  ring

omit [DecidableEq b] in
lemma herm_target (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (lam : ℝ) (hC : C.IsHermitian) (hF : Fbar.IsHermitian) :
    (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).IsHermitian := by
  apply herm_of_transpose
  rw [transpose_neg, transpose_add, transpose_add, transpose_smul, transpose_smul,
    transpose_mul, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
    transpose_of_herm hC, transpose_of_herm hF, Matrix.mul_assoc]

omit [DecidableEq b] in
lemma herm_unc (C : Matrix a a ℝ) (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ)
    (hC : C.IsHermitian) : (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).IsHermitian := by
  apply herm_of_transpose
  rw [transpose_neg, transpose_add, transpose_add, transpose_of_herm hC]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  abel

omit [DecidableEq b] in
/-- Reverse direction: the multiplier bound dominates every admissible `F`. -/
lemma rev_le (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (lam : ℝ) (hlam : 0 < lam) (F : Matrix b c ℝ) (hF : F ∈ (QuadMatIneq.Petersen.uncSet Fbar :
      Set (Matrix b c ℝ))) (x : a → ℝ) :
    x ⬝ᵥ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))) *ᵥ x ≤
      x ⬝ᵥ (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)) *ᵥ x := by
  rw [qf_target, qf_unc]
  have hF' : (F *ᵥ (G *ᵥ x)) ⬝ᵥ (F *ᵥ (G *ᵥ x)) ≤ (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) := by
    have := hF.dotProduct_mulVec_nonneg (G *ᵥ x)
    rw [star_trivial, sub_mulVec, dotProduct_sub, qf_transpose_mul] at this
    linarith
  have h1 := dot_self_nonneg (lam • (Eᵀ *ᵥ x) - F *ᵥ (G *ᵥ x))
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, dotProduct_comm (F *ᵥ (G *ᵥ x)) (Eᵀ *ᵥ x)] at h1
  simp only [smul_eq_mul] at h1
  exact scal_rev lam _ _ _ _ _ hlam (by linarith [h1]) hF'

omit [DecidableEq b] in
lemma exists_F_of (Fbar : Matrix c c ℝ) (hFbar : Fbar.PosSemidef) (G : Matrix c a ℝ)
    (x : a → ℝ) (w : b → ℝ) (h : 0 ≤ (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) - w ⬝ᵥ w) :
    ∃ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)), F *ᵥ (G *ᵥ x) = w := by
  obtain ⟨F, hF, hFu⟩ := exists_F Fbar hFbar (G *ᵥ x) w (by linarith)
  exact ⟨F, hF, hFu⟩

omit [DecidableEq b] in
lemma rev_strict (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (hC : C.IsHermitian) (lam : ℝ) (hlam : 0 < lam)
    (hPD : (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef) :
    ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef := fun F hF =>
  posDef_iff_dotProduct_mulVec.mpr ⟨herm_unc _ _ _ _ hC, fun x hx => by
    have := (posDef_iff_dotProduct_mulVec.mp hPD).2 hx
    rw [star_trivial] at this ⊢
    exact lt_of_lt_of_le this (rev_le C E Fbar G lam hlam F hF x)⟩

omit [DecidableEq b] in
lemma rev_nonstrict (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (lam : ℝ) (hlam : 0 < lam)
    (hPSD : (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef) :
    ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef := fun F hF =>
  posSemidef_iff_dotProduct_mulVec.mpr ⟨herm_unc _ _ _ _ hC, fun x => by
    have := hPSD.dotProduct_mulVec_nonneg x
    rw [star_trivial] at this ⊢
    exact le_trans this (rev_le C E Fbar G lam hlam F hF x)⟩

lemma fwd_strict [DecidableEq a] (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef)
    (h : ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef := by
  have hcond : ∀ y : a ⊕ b → ℝ, y ≠ 0 → 0 ≤ y ⬝ᵥ MB Fbar G *ᵥ y →
      0 < y ⬝ᵥ MA C E *ᵥ y := by
    intro y hy hB
    rw [← Sum.elim_comp_inl_inr y] at hy hB ⊢
    rw [qB] at hB
    rw [qA]
    obtain ⟨F, hF, hFu⟩ := exists_F_of Fbar hFbar G _ _ hB
    by_cases hx : y ∘ Sum.inl = 0
    · exfalso
      rw [hx, mulVec_zero, zero_dotProduct] at hB
      have hw : y ∘ Sum.inr = 0 :=
        dotProduct_self_eq_zero.mp (le_antisymm (by linarith) (dot_self_nonneg _))
      rw [hx, hw] at hy
      exact hy (by simp)
    · have := (posDef_iff_dotProduct_mulVec.mp (h F hF)).2 hx
      rw [star_trivial, qf_unc, hFu] at this
      linarith
  obtain ⟨τ, hτ, hq⟩ := sLemma_strict_pos (MA_symm C E hC) (MB_symm Fbar G hFbar.1) hcond
  refine ⟨τ⁻¹, inv_pos.mpr hτ, posDef_iff_dotProduct_mulVec.mpr
    ⟨herm_target _ _ _ _ _ hC hFbar.1, fun x hx => ?_⟩⟩
  rw [star_trivial, qf_target, inv_inv]
  have hy : Sum.elim x (τ⁻¹ • (Eᵀ *ᵥ x)) ≠ 0 := by
    intro h0; apply hx; have := congrArg (fun z => z ∘ Sum.inl) h0; simpa using this
  have := hq _ hy
  rw [qA, qB] at this
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
  linarith [scal_fwd τ (x ⬝ᵥ C *ᵥ x) ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x))
    ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) hτ]

lemma fwd_nonstrict [DecidableEq a] (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (hE : E ≠ 0) (hFpd : Fbar.PosDef) (hG : G ≠ 0)
    (h : ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) :
    ∃ lam : ℝ, 0 < lam ∧
      (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef := by
  have hFbar : Fbar.PosSemidef := hFpd.posSemidef
  have hslater : ∃ y : a ⊕ b → ℝ, 0 < y ⬝ᵥ MB Fbar G *ᵥ y := by
    obtain ⟨j, hj⟩ : ∃ j, G *ᵥ Pi.single j 1 ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      apply hG
      ext i j
      have := congrFun (hcon j) i
      simpa [mulVec_single_one] using this
    refine ⟨Sum.elim (Pi.single j 1) 0, ?_⟩
    rw [qB, dotProduct_zero, sub_zero]
    have := (posDef_iff_dotProduct_mulVec.mp hFpd).2 hj
    rwa [star_trivial] at this
  have hcond : ∀ y : a ⊕ b → ℝ, 0 ≤ y ⬝ᵥ MB Fbar G *ᵥ y → 0 ≤ y ⬝ᵥ MA C E *ᵥ y := by
    intro y hB
    rw [← Sum.elim_comp_inl_inr y] at hB ⊢
    rw [qB] at hB
    rw [qA]
    obtain ⟨F, hF, hFu⟩ := exists_F_of Fbar hFbar G _ _ hB
    have := (h F hF).dotProduct_mulVec_nonneg (y ∘ Sum.inl)
    rw [star_trivial, qf_unc, hFu] at this
    linarith
  obtain ⟨τ, hτ0, hPSD⟩ :=
    (DualityKit.Matrix.sLemma (MA_symm C E hC) (MB_symm Fbar G hFbar.1) hslater).mp hcond
  have hq : ∀ y, 0 ≤ y ⬝ᵥ MA C E *ᵥ y - τ * (y ⬝ᵥ MB Fbar G *ᵥ y) := fun y => by
    have := hPSD.dotProduct_mulVec_nonneg y
    rwa [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at this
  have hτ : 0 < τ := by
    rcases hτ0.eq_or_lt with h0 | h0
    swap
    · exact h0
    exfalso
    apply hE
    apply mulVec_injective
    funext w
    rw [zero_mulVec]
    have hd : (Eᵀ *ᵥ (E *ᵥ w)) ⬝ᵥ w = (E *ᵥ w) ⬝ᵥ (E *ᵥ w) := by rw [← dot_mulVec_eq]
    have key := scal_zero ((E *ᵥ w) ⬝ᵥ C *ᵥ (E *ᵥ w)) ((E *ᵥ w) ⬝ᵥ (E *ᵥ w))
      (dot_self_nonneg _) (fun t => by
        have := hq (Sum.elim (t • (E *ᵥ w)) w)
        rw [← h0, qA, zero_mul, sub_zero] at this
        simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hd] at this
        linarith)
    exact dotProduct_self_eq_zero.mp key
  refine ⟨τ⁻¹, inv_pos.mpr hτ, posSemidef_iff_dotProduct_mulVec.mpr
    ⟨herm_target _ _ _ _ _ hC hFbar.1, fun x => ?_⟩⟩
  rw [star_trivial, qf_target, inv_inv]
  have := hq (Sum.elim x (τ⁻¹ • (Eᵀ *ᵥ x)))
  rw [qA, qB] at this
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
  linarith [scal_fwd τ (x ⬝ᵥ C *ᵥ x) ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x))
    ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) hτ]

end Main

end RRAux_QuadMatIneq_Petersen_proposition_4_16

open QuadMatIneq.Petersen in
open Matrix in
theorem solution {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (E : Matrix (Fin n) (Fin p) ℝ) (Fbar : Matrix (Fin q) (Fin q) ℝ)
    (G : Matrix (Fin q) (Fin n) ℝ) (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) :
    ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
        (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) ↔
      ∃ lam : ℝ, 0 < lam ∧ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef) ∧
    (E ≠ 0 → Fbar.PosDef → G ≠ 0 →
      ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
          (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) ↔
        ∃ lam : ℝ, 0 < lam ∧
          (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef)) := by
  refine ⟨⟨RRAux_QuadMatIneq_Petersen_proposition_4_16.fwd_strict C E Fbar G hC hFbar,
    fun ⟨lam, hlam, h⟩ =>
      RRAux_QuadMatIneq_Petersen_proposition_4_16.rev_strict C E Fbar G hC lam hlam h⟩,
    fun hE hFpd hG => ⟨RRAux_QuadMatIneq_Petersen_proposition_4_16.fwd_nonstrict C E Fbar G hC
      hE hFpd hG, fun ⟨lam, hlam, h⟩ =>
        RRAux_QuadMatIneq_Petersen_proposition_4_16.rev_nonstrict C E Fbar G hC lam hlam h⟩⟩

#print axioms solution
