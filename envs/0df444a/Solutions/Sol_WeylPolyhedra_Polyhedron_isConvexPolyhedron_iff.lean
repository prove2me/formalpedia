-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.isConvexPolyhedron_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:12:14.995807+00:00
-- url     : https://prove2.me/submissions/f32d88fc-31c2-416b-b0c3-18f638f48cb6

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope



namespace WeylPolyhedra.Polyhedron

open Matrix Module

lemma wp_rep_mono {n : ℕ} {T S : Finset (Fin n → ℝ)} (h : T ⊆ S) {x : Fin n → ℝ}
    (hx : Shared.Representable T x) : Shared.Representable S x := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨fun v => if v ∈ T then c v else 0, fun s _ => ?_, ?_⟩
  · dsimp only
    split_ifs with h'
    · exact hc s h'
    · exact le_rfl
  rw [← Finset.sum_subset h (fun v _ hv => by simp [hv])]
  exact Finset.sum_congr rfl fun v hv => by simp [hv]

lemma wp_rep_self {n : ℕ} {S : Finset (Fin n → ℝ)} {s : Fin n → ℝ} (hs : s ∈ S) :
    Shared.Representable S s := by
  classical
  refine ⟨fun v => if v = s then 1 else 0, fun _ _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp [ite_smul, hs]

lemma wp_rep_smul {n : ℕ} {S : Finset (Fin n → ℝ)} {t : ℝ} (ht : 0 ≤ t) {y : Fin n → ℝ}
    (hy : Shared.Representable S y) : Shared.Representable S (t • y) := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨fun s => t * c s, fun s hs => mul_nonneg ht (hc s hs), ?_⟩
  simp [Finset.smul_sum, mul_smul]

lemma wp_cone_convex {n : ℕ} (S : Finset (Fin n → ℝ)) :
    Convex ℝ {x | Shared.Representable S x} := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩ a b ha hb _
  refine ⟨fun s => a * c s + b * d s,
    fun s hs => add_nonneg (mul_nonneg ha (hc s hs)) (mul_nonneg hb (hd s hs)), ?_⟩
  simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma wp_cara {n : ℕ} (x : Fin n → ℝ) : ∀ (k : ℕ) (S : Finset (Fin n → ℝ)), S.card = k →
    Shared.Representable S x →
    ∃ T ⊆ S, LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ Shared.Representable T x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk ⟨c, hc0, hx⟩
  by_cases hli : LinearIndependent ℝ (fun t : S => (t : Fin n → ℝ))
  · exact ⟨S, subset_rfl, hli, c, hc0, hx⟩
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  classical
  let G : (Fin n → ℝ) → ℝ := fun v => if h : v ∈ S then g ⟨v, h⟩ else 0
  have hG : ∑ s ∈ S, G s • s = 0 := by
    rw [← hg, ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun s _ => by simp [G, s.2]
  have hGi : G i ≠ 0 := by simpa [G, i.2] using hi
  obtain ⟨H, hH, s1, hs1, hpos⟩ : ∃ H : (Fin n → ℝ) → ℝ, ∑ s ∈ S, H s • s = 0 ∧
      ∃ s1 ∈ S, 0 < H s1 := by
    rcases lt_or_gt_of_ne hGi with h | h
    · refine ⟨fun v => - G v, ?_, i, i.2, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, hG]
    · exact ⟨G, hG, i, i.2, h⟩
  let P := S.filter (fun s => 0 < H s)
  obtain ⟨s0, hs0P, hmin⟩ := P.exists_min_image (fun s => c s / H s)
    ⟨s1, by simp [P, hs1, hpos]⟩
  have hs0 : s0 ∈ S ∧ 0 < H s0 := by simpa [P] using hs0P
  set t := c s0 / H s0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 s0 hs0.1) hs0.2.le
  let c' : (Fin n → ℝ) → ℝ := fun s => c s - t * H s
  have hc' : ∀ s ∈ S, 0 ≤ c' s := by
    intro s hs
    by_cases hHs : 0 < H s
    · have := hmin s (by simp [P, hs, hHs])
      rw [le_div_iff₀ hHs] at this
      simp only [c']; linarith
    · push_neg at hHs
      have := hc0 s hs
      simp only [c']; nlinarith
  have hc's0 : c' s0 = 0 := by
    simp only [c', t]; rw [div_mul_cancel₀ _ hs0.2.ne']; ring
  have hx' : x = ∑ s ∈ S.erase s0, c' s • s := by
    rw [Finset.sum_erase S (by simp [hc's0])]
    simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hH, hx]
    simp
  obtain ⟨T, hTS, hTli, hTr⟩ := ih _ (by rw [← hk]; exact Finset.card_erase_lt_of_mem hs0.1)
    (S.erase s0) rfl ⟨c', fun s hs => hc' s (Finset.mem_of_mem_erase hs), hx'⟩
  exact ⟨T, hTS.trans (Finset.erase_subset _ _), hTli, hTr⟩

lemma wp_cone_indep_closed {n : ℕ} (T : Finset (Fin n → ℝ))
    (hT : LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ))) :
    IsClosed {x | Shared.Representable T x} := by
  classical
  let L : (T → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Fintype.linearCombination ℝ (fun t : T => (t : Fin n → ℝ))
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := Fintype.linearIndependent_iff.1 hT m (by simpa [L, Fintype.linearCombination_apply] using hm)
    funext i; exact this i
  have hset : {x | Shared.Representable T x} = L '' {c | ∀ i, 0 ≤ c i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c i, fun i => hc i i.2, ?_⟩
      simp only [L, Fintype.linearCombination_apply]
      exact Finset.sum_coe_sort T (fun s => c s • s)
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun v => if h : v ∈ T then c ⟨v, h⟩ else 0, fun s hs => by simp [hs, hc], ?_⟩
      simp only [L, Fintype.linearCombination_apply]
      rw [← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl fun s _ => by simp [s.2]
  rw [hset]
  apply (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma wp_cone_closed {n : ℕ} (S : Finset (Fin n → ℝ)) :
    IsClosed {x | Shared.Representable S x} := by
  classical
  let F : Finset (Finset (Fin n → ℝ)) := S.powerset.filter
      (fun T : Finset (Fin n → ℝ) => LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)))
  have : {x | Shared.Representable S x} = ⋃ T ∈ F, {x | Shared.Representable T x} := by
    ext x
    simp only [F, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      obtain ⟨T, hTS, hli, hr⟩ := wp_cara x _ S rfl h
      exact ⟨T, ⟨hTS, hli⟩, hr⟩
    · rintro ⟨T, ⟨hTS, _⟩, hr⟩
      exact wp_rep_mono hTS hr
  rw [this]
  exact isClosed_biUnion_finset fun T hT => wp_cone_indep_closed T (Finset.mem_filter.1 hT).2

lemma wp_farkas {n : ℕ} (S : Finset (Fin n → ℝ)) (x : Fin n → ℝ)
    (hx : ¬ Shared.Representable S x) :
    ∃ p : Fin n → ℝ, (∀ s ∈ S, 0 ≤ p ⬝ᵥ s) ∧ p ⬝ᵥ x < 0 := by
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point (wp_cone_convex S)
    (wp_cone_closed S) (show x ∉ {x | Shared.Representable S x} from hx)
  have h0 : Shared.Representable S 0 := ⟨0, fun _ _ => le_rfl, by simp⟩
  have hu : 0 < u := by simpa using hfu 0 h0
  have hle : ∀ y, Shared.Representable S y → f y ≤ 0 := by
    intro y hy
    by_contra hpos
    push_neg at hpos
    have hmem : Shared.Representable S ((u / f y) • y) := wp_rep_smul (by positivity) hy
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    exact lt_irrefl _ this
  let p : Fin n → ℝ := fun i => - f (fun j => if i = j then 1 else 0)
  have hp : ∀ y, p ⬝ᵥ y = - f y := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ y]
    simp [p, map_sum, dotProduct, mul_comm, Finset.sum_neg_distrib]
  refine ⟨p, fun s hs => ?_, ?_⟩
  · rw [hp]; have := hle s (wp_rep_self hs); linarith
  · rw [hp]; linarith


def wpDotL {n : ℕ} (d : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun w := d ⬝ᵥ w
  map_add' := by intro x y; simp [dotProduct_add]
  map_smul' := by intro c x; simp [dotProduct_smul]

lemma wp_dot_span_zero {n : ℕ} {d : Fin n → ℝ} {T : Set (Fin n → ℝ)}
    (h : ∀ t ∈ T, d ⬝ᵥ t = 0) {w : Fin n → ℝ} (hw : w ∈ Submodule.span ℝ T) : d ⬝ᵥ w = 0 := by
  have : Submodule.span ℝ T ≤ LinearMap.ker (wpDotL d) :=
    Submodule.span_le.2 (fun t ht => by simpa [wpDotL] using h t ht)
  simpa [wpDotL] using this hw

lemma wp_ker_dim {n : ℕ} (T : Finset (Fin n → ℝ)) :
    finrank ℝ (LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ))))) +
      finrank ℝ (Submodule.span ℝ (T : Set (Fin n → ℝ))) = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ))))
  have h2 := Matrix.rank_eq_finrank_span_row (Matrix.of (fun t : T => (t : Fin n → ℝ)))
  unfold Matrix.rank at h2
  have h3 : Set.range (Matrix.row (Matrix.of (fun t : T => (t : Fin n → ℝ)))) = (T : Set (Fin n → ℝ)) := by
    ext v
    simp only [Matrix.row, Set.mem_range, Matrix.of_apply, Finset.mem_coe]
    constructor
    · rintro ⟨t, rfl⟩; exact t.2
    · intro hv; exact ⟨⟨v, hv⟩, rfl⟩
  rw [h3] at h2
  rw [Module.finrank_fin_fun] at h1
  omega

lemma wp_ker_mem {n : ℕ} {T : Finset (Fin n → ℝ)} {d : Fin n → ℝ} :
    d ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ)))) ↔ ∀ t ∈ T, t ⬝ᵥ d = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h t ht
    have := congrFun h ⟨t, ht⟩
    simpa [Matrix.mulVec] using this
  · intro h
    funext t
    simpa [Matrix.mulVec] using h t t.2

lemma wp_exists_orth {n : ℕ} (T : Finset (Fin n → ℝ))
    (h : finrank ℝ (Submodule.span ℝ (T : Set (Fin n → ℝ))) < n) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ t ∈ T, t ⬝ᵥ d = 0 := by
  have := wp_ker_dim T
  have hne : LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ)))) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at this
    omega
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨d, hd0, wp_ker_mem.1 hd⟩

lemma wp_finrank_insert {n : ℕ} (x : Fin n → ℝ) (T : Set (Fin n → ℝ)) :
    finrank ℝ (Submodule.span ℝ (insert x T)) ≤ finrank ℝ (Submodule.span ℝ T) + 1 := by
  rw [Submodule.span_insert]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ x) (Submodule.span ℝ T)
  have h2 : finrank ℝ (ℝ ∙ x) ≤ 1 := by
    have := finrank_span_le_card (R := ℝ) ({x} : Set (Fin n → ℝ))
    simpa using this
  omega

lemma wp_vertex {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (x : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ s ∈ S, 0 ≤ p ⬝ᵥ s) (hpx : p ⬝ᵥ x < 0) :
    ∀ k, k ≤ n - 1 → ∃ α : Fin n → ℝ, (∀ s ∈ S, 0 ≤ α ⬝ᵥ s) ∧ α ⬝ᵥ x < 0 ∧
      k ≤ finrank ℝ (Submodule.span ℝ
        ((S.filter fun s => α ⬝ᵥ s = 0 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
  | 0, _ => ⟨p, hp, hpx, Nat.zero_le _⟩
  | k+1, hk => by
    obtain ⟨α, hα, hαx, hr⟩ := wp_vertex S hS x p hp hpx k (by omega)
    by_cases hlt : k + 1 ≤ finrank ℝ (Submodule.span ℝ
        ((S.filter fun s => α ⬝ᵥ s = 0 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
    · exact ⟨α, hα, hαx, hlt⟩
    classical
    set T := S.filter (fun s => α ⬝ᵥ s = 0) with hT
    have hrk : finrank ℝ (Submodule.span ℝ (T : Set (Fin n → ℝ))) = k := by omega
    have hins := wp_finrank_insert x (T : Set (Fin n → ℝ))
    obtain ⟨d, hd0, hdT⟩ := wp_exists_orth (insert x T) (by
      rw [Finset.coe_insert]; omega)
    have hdx : d ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hdT x (Finset.mem_insert_self _ _)
    have hdt : ∀ t ∈ T, d ⬝ᵥ t = 0 := fun t ht => by
      rw [dotProduct_comm]; exact hdT t (Finset.mem_insert_of_mem ht)
    have hex : ∃ s ∈ S, d ⬝ᵥ s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd0 (hS d h)
    obtain ⟨e, he0, hex, s1, hs1, hs1neg⟩ : ∃ e : Fin n → ℝ, (∀ t ∈ T, e ⬝ᵥ t = 0) ∧
        e ⬝ᵥ x = 0 ∧ ∃ s1 ∈ S, e ⬝ᵥ s1 < 0 := by
      obtain ⟨s, hs, hds⟩ := hex
      rcases lt_or_gt_of_ne hds with h | h
      · exact ⟨d, hdt, hdx, s, hs, h⟩
      · refine ⟨-d, fun t ht => by simp [neg_dotProduct, hdt t ht], by simp [neg_dotProduct, hdx],
          s, hs, by simp [neg_dotProduct]; linarith⟩
    let N := S.filter (fun s => e ⬝ᵥ s < 0)
    obtain ⟨s0, hs0N, hmin⟩ := N.exists_min_image (fun s => α ⬝ᵥ s / (-(e ⬝ᵥ s)))
      ⟨s1, by simp [N, hs1, hs1neg]⟩
    have hs0 : s0 ∈ S ∧ e ⬝ᵥ s0 < 0 := by simpa [N] using hs0N
    set τ := α ⬝ᵥ s0 / (-(e ⬝ᵥ s0)) with hτdef
    have hτ : 0 ≤ τ := div_nonneg (hα s0 hs0.1) (by linarith)
    have hτe : τ * (e ⬝ᵥ s0) = - (α ⬝ᵥ s0) := by
      rw [hτdef, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    refine ⟨α + τ • e, ?_, ?_, ?_⟩
    · intro s hs
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      by_cases hneg : e ⬝ᵥ s < 0
      · have := hmin s (by simp [N, hs, hneg])
        rw [le_div_iff₀ (by linarith)] at this
        linarith
      · push_neg at hneg
        have := hα s hs
        nlinarith
    · rw [add_dotProduct, smul_dotProduct, hex]; simpa using hαx
    · have hsub : Submodule.span ℝ (T : Set (Fin n → ℝ)) < Submodule.span ℝ
          ((S.filter fun s => (α + τ • e) ⬝ᵥ s = 0 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
        rw [SetLike.lt_iff_le_and_exists]
        refine ⟨Submodule.span_mono ?_, s0, Submodule.subset_span ?_, ?_⟩
        · intro t ht
          have ht' : t ∈ S ∧ α ⬝ᵥ t = 0 := by simpa [hT] using ht
          simp only [Finset.coe_filter, Set.mem_setOf_eq]
          refine ⟨ht'.1, ?_⟩
          rw [add_dotProduct, smul_dotProduct, ht'.2, he0 t ht]; simp
        · simp only [Finset.coe_filter, Set.mem_setOf_eq]
          refine ⟨hs0.1, ?_⟩
          rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hτe]; ring
        · intro hmem
          have := wp_dot_span_zero he0 hmem
          linarith [hs0.2]
      have := Submodule.finrank_lt_finrank_of_lt hsub
      omega

theorem hauptsatz_core {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (x : Fin n → ℝ) (hx : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ x) :
    Shared.Representable S x := by
  classical
  by_contra hnot
  obtain ⟨p, hp, hpx⟩ := wp_farkas S x hnot
  obtain ⟨α, hα, hαx, hr⟩ := wp_vertex S hS x p hp hpx (n - 1) le_rfl
  set T := S.filter (fun s => α ⬝ᵥ s = 0) with hT
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent ℝ (T : Set (Fin n → ℝ))
  have hbfin : b.Finite := T.finite_toSet.subset hbT
  set B := hbfin.toFinset with hB
  have hBb : (B : Set (Fin n → ℝ)) = b := by simp [hB]
  have hliB : LinearIndepOn ℝ id (B : Set (Fin n → ℝ)) := by rw [hBb]; exact hli
  have hcard : B.card = finrank ℝ (Submodule.span ℝ (T : Set (Fin n → ℝ))) := by
    rw [← hspan, ← hBb, finrank_span_finset_eq_card hliB]
  obtain ⟨T0, hT0B, hT0card⟩ := Finset.exists_subset_card_eq (show n - 1 ≤ B.card by omega)
  have hT0T : T0 ⊆ T := by
    intro t ht
    have : t ∈ b := by rw [← hBb]; exact hT0B ht
    exact hbT this
  have hli0 : LinearIndepOn ℝ id (T0 : Set (Fin n → ℝ)) :=
    hliB.mono (by exact_mod_cast hT0B)
  have hα0 : α ≠ 0 := by rintro rfl; simp at hαx
  have hext : Shared.IsExtremeSupport S α := by
    refine ⟨⟨hα0, hα⟩, T0, hT0T.trans (Finset.filter_subset _ _), hT0card, hli0, ?_⟩
    intro t ht
    exact (Finset.mem_filter.1 (hT0T ht)).2
  have := hx α hext
  linarith


lemma wp_dot_sum {n : ℕ} (α : Fin n → ℝ) (S : Finset (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ) :
    α ⬝ᵥ (∑ s ∈ S, c s • s) = ∑ s ∈ S, c s * (α ⬝ᵥ s) := by
  have := map_sum (wpDotL α) (fun s => c s • s) S
  simp only [wpDotL, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, smul_eq_mul] at this
  exact this

theorem zusatz_core {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) :
    (¬ ∃ α : Fin n → ℝ, Shared.IsExtremeSupport S α) ↔
      ∃ c : (Fin n → ℝ) → ℝ, (∀ s ∈ S, 0 < c s) ∧ (0 : Fin n → ℝ) = ∑ s ∈ S, c s • s := by
  constructor
  · intro h
    obtain ⟨c, hc, hx⟩ := hauptsatz_core S hS (-(∑ s ∈ S, s))
      (fun α hα => absurd ⟨α, hα⟩ h)
    refine ⟨fun s => c s + 1, fun s hs => by have := hc s hs; linarith, ?_⟩
    simp only [add_smul, one_smul, Finset.sum_add_distrib, ← hx]
    simp
  · rintro ⟨c, hc, h0⟩ ⟨α, ⟨hα0, hαS⟩, _⟩
    have h1 := wp_dot_sum α S c
    rw [← h0, dotProduct_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s hs => mul_nonneg (hc s hs).le (hαS s hs))).1 h1.symm
    apply hα0
    apply hS α
    intro s hs
    have := h2 s hs
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc s hs).ne'
    · exact h

lemma wp_sol_iff_support {n : ℕ} (S : Finset (Fin n → ℝ)) (α : Fin n → ℝ) :
    IsExtremeSolution S α ↔ Shared.IsExtremeSupport S α := by
  constructor
  · rintro ⟨hsol, hne, T, hTS, hcard, hli, hT⟩
    exact ⟨⟨hne, fun s hs => by rw [dotProduct_comm]; exact hsol s hs⟩, T, hTS, hcard, hli,
      fun t ht => by rw [dotProduct_comm]; exact hT t ht⟩
  · rintro ⟨⟨hne, hsup⟩, T, hTS, hcard, hli, hT⟩
    exact ⟨fun s hs => by rw [dotProduct_comm]; exact hsup s hs, hne, T, hTS, hcard, hli,
      fun t ht => by rw [dotProduct_comm]; exact hT t ht⟩

theorem satz6_core {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (p : Fin n → ℝ) :
    p ∈ dualRegion S ↔ ∀ ξ ∈ solutionRegion S, 0 ≤ p ⬝ᵥ ξ := by
  constructor
  · intro hp ξ hξ
    obtain ⟨c, hc, rfl⟩ := hauptsatz_core S hS p
      (fun α hα => hp α ((wp_sol_iff_support S α).2 hα))
    rw [dotProduct_comm, wp_dot_sum]
    exact Finset.sum_nonneg fun s hs => mul_nonneg (hc s hs) (by rw [dotProduct_comm]; exact hξ s hs)
  · intro h α hα
    rw [dotProduct_comm]
    exact h α hα.1


lemma wp_ker1 {n : ℕ} (T : Finset (Fin n → ℝ))
    (hli : LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ))) (hcard : T.card = n - 1)
    {ξ ξ' : Fin n → ℝ} (hξ0 : ξ ≠ 0) (hξ : ∀ a ∈ T, a ⬝ᵥ ξ = 0) (hξ' : ∀ a ∈ T, a ⬝ᵥ ξ' = 0) :
    ∃ c : ℝ, ξ' = c • ξ := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim ξ 0) hξ0
    · exact h
  have hdim := wp_ker_dim T
  have hsp : finrank ℝ (Submodule.span ℝ (T : Set (Fin n → ℝ))) = T.card :=
    finrank_span_finset_eq_card (by exact hli)
  have hK : finrank ℝ (LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ))))) = 1 := by
    omega
  have hmem : ξ ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ)))) :=
    wp_ker_mem.2 hξ
  have hmem' : ξ' ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ)))) :=
    wp_ker_mem.2 hξ'
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨ξ, hmem⟩ :
    LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun t : T => (t : Fin n → ℝ)))))
    (by intro h; apply hξ0; exact congrArg Subtype.val h)).1 hK ⟨ξ', hmem'⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma wp_finite_extreme {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) :
    ∃ E : Finset (Fin n → ℝ), (∀ e ∈ E, IsExtremeSolution S e) ∧
      ∀ α, IsExtremeSolution S α → ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧ α = c • e := by
  classical
  let P : Finset (Fin n → ℝ) → Prop := fun T =>
    ∃ ξ, ξ ∈ solutionRegion S ∧ ξ ≠ 0 ∧ ∀ a ∈ T, a ⬝ᵥ ξ = 0
  let g : Finset (Fin n → ℝ) → (Fin n → ℝ) := fun T => if h : P T then h.choose else 0
  let F : Finset (Finset (Fin n → ℝ)) := S.powerset.filter (fun T : Finset (Fin n → ℝ) => T.card = n - 1 ∧
    LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ P T)
  have hg : ∀ T ∈ F, g T ∈ solutionRegion S ∧ g T ≠ 0 ∧ ∀ a ∈ T, a ⬝ᵥ g T = 0 := by
    intro T hT
    have hPT : P T := (Finset.mem_filter.1 hT).2.2.2
    simp only [g, dif_pos hPT]
    exact hPT.choose_spec
  refine ⟨F.image g, ?_, ?_⟩
  · intro e he
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h3⟩ := hg T hT
    have hT' := Finset.mem_filter.1 hT
    exact ⟨h1, h2, T, Finset.mem_powerset.1 hT'.1, hT'.2.1, hT'.2.2.1, h3⟩
  · rintro α ⟨hα, hα0, T, hTS, hcard, hli, hT⟩
    have hTF : T ∈ F := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hTS, hcard, hli,
      ⟨α, hα, hα0, hT⟩⟩
    obtain ⟨h1, h2, h3⟩ := hg T hTF
    obtain ⟨c, hc⟩ := wp_ker1 T hli hcard h2 h3 hT
    refine ⟨g T, Finset.mem_image_of_mem g hTF, c, ?_, hc⟩
    rcases lt_trichotomy c 0 with hneg | hz | hpos
    · exfalso
      apply h2
      apply hS
      intro s hs
      have e1 := hα s hs
      have e2 := h1 s hs
      rw [hc, dotProduct_smul, smul_eq_mul] at e1
      rw [dotProduct_comm]
      nlinarith
    · exfalso; apply hα0; rw [hc, hz, zero_smul]
    · exact hpos

theorem representation_core {n : ℕ} (S : Finset (Fin n → ℝ))
    (hS : Shared.NonDegenerate S) (π : Fin n → ℝ) (hπ : π ∈ solutionRegion S) :
    ∃ E : Finset (Fin n → ℝ), (∀ e ∈ E, IsExtremeSolution S e) ∧
      ∃ l : (Fin n → ℝ) → ℝ, (∀ e ∈ E, 0 ≤ l e) ∧ π = ∑ e ∈ E, l e • e := by
  obtain ⟨E, hE, hall⟩ := wp_finite_extreme S hS
  refine ⟨E, hE, ?_⟩
  by_contra hnot
  obtain ⟨p, hp, hpπ⟩ := wp_farkas E π hnot
  have hdual : p ∈ dualRegion S := by
    intro α hα
    obtain ⟨e, he, c, hc, rfl⟩ := hall α hα
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]
    exact mul_nonneg hc.le (hp e he)
  have := (satz6_core S hS p).1 hdual π hπ
  linarith

theorem satz9_core {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ p : Fin n → ℝ, (∀ α : Fin n → ℝ, IsExtremeSolution S α → α ⬝ᵥ p = 0) → p = 0 := by
  obtain ⟨ξ₀, hξ₀⟩ := hint
  intro p hp
  have hzero : ∀ ξ ∈ solutionRegion S, p ⬝ᵥ ξ = 0 := by
    intro ξ hξ
    obtain ⟨E, hE, l, hl, rfl⟩ := representation_core S hS ξ hξ
    rw [wp_dot_sum]
    exact Finset.sum_eq_zero fun e he => by rw [dotProduct_comm, hp e (hE e he), mul_zero]
  have h0 := hzero ξ₀ (fun a ha => (hξ₀ a ha).le)
  set t : ℝ := ∑ a ∈ S, |a ⬝ᵥ p| / (a ⬝ᵥ ξ₀) with ht
  have hmem : t • ξ₀ + p ∈ solutionRegion S := by
    intro a ha
    have hpos := hξ₀ a ha
    have hle : |a ⬝ᵥ p| / (a ⬝ᵥ ξ₀) ≤ t :=
      Finset.single_le_sum (f := fun a => |a ⬝ᵥ p| / (a ⬝ᵥ ξ₀))
        (fun b hb => div_nonneg (abs_nonneg _) (hξ₀ b hb).le) ha
    rw [div_le_iff₀ hpos] at hle
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have := neg_abs_le (a ⬝ᵥ p)
    linarith
  have h1 := hzero _ hmem
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, h0, mul_zero, zero_add] at h1
  exact dotProduct_self_eq_zero.1 h1


def wlift {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.snoc x (-1)

lemma wp_dot_snoc {m : ℕ} (a x : Fin m → ℝ) (a0 y : ℝ) :
    (Fin.snoc a a0 : Fin (m+1) → ℝ) ⬝ᵥ (Fin.snoc x y : Fin (m+1) → ℝ) = a ⬝ᵥ x + a0 * y := by
  simp [dotProduct, Fin.sum_univ_castSucc]

lemma wp_dot_wlift {m : ℕ} (α : Fin (m+1) → ℝ) (x : Fin m → ℝ) :
    α ⬝ᵥ wlift x = Fin.init α ⬝ᵥ x - α (Fin.last m) := by
  conv_lhs => rw [← Fin.snoc_init_self α]
  rw [wlift, wp_dot_snoc]; ring

lemma wp_sum_snoc {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Fin m → ℝ)
    (g : ι → ℝ) : ∑ i ∈ s, c i • (Fin.snoc (f i) (g i) : Fin (m+1) → ℝ) =
      Fin.snoc (∑ i ∈ s, c i • f i) (∑ i ∈ s, c i * g i) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [Finset.sum_apply]
  | cast j => simp [Finset.sum_apply]

lemma wp_snoc_zero {m : ℕ} : (Fin.snoc (0 : Fin m → ℝ) (0 : ℝ) : Fin (m+1) → ℝ) = 0 := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

lemma wlift_injective {m : ℕ} : Function.Injective (wlift (m := m)) := by
  intro x y h
  have := congrArg Fin.init h
  simpa [wlift, Fin.init_snoc] using this

lemma wp_ext_to_affine {m : ℕ} (S : Finset (Fin m → ℝ)) (α : Fin (m+1) → ℝ)
    (h : Shared.IsExtremeSupport (S.image wlift) α) :
    IsExtremeAffineSupport S (Fin.init α) (α (Fin.last m)) := by
  classical
  obtain ⟨⟨hα0, hsup⟩, T, hTS, hcard, hli, hT⟩ := h
  have hTT : ∀ t ∈ T, wlift (Fin.init t) = t := by
    intro t ht
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 (hTS ht)
    simp [wlift, Fin.init_snoc]
  refine ⟨?_, ?_, T.image Fin.init, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hα0
    rw [← Fin.snoc_init_self α, hc.1, hc.2, wp_snoc_zero]
  · intro s hs
    have := hsup (wlift s) (Finset.mem_image_of_mem _ hs)
    rwa [wp_dot_wlift] at this
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (hTS ht0)
    simpa [wlift, Fin.init_snoc] using hs
  · rw [Finset.card_image_of_injOn, hcard]
    · simp
    · intro x hx y hy hxy
      rw [← hTT x hx, ← hTT y hy]
      exact congrArg wlift hxy
  · rw [affineIndependent_iff_of_fintype]
    intro w hw0 hwv
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
      Finset.weightedVSubOfPoint_apply] at hwv
    simp only [vsub_eq_sub, sub_zero] at hwv
    let e : T ≃ (T.image Fin.init) :=
      { toFun := fun t => ⟨Fin.init (t : Fin (m+1) → ℝ), Finset.mem_image_of_mem _ t.2⟩
        invFun := fun t => ⟨wlift (t : Fin m → ℝ), by
          obtain ⟨t0, ht0, h⟩ := Finset.mem_image.1 t.2
          rw [← h, hTT t0 ht0]; exact ht0⟩
        left_inv := fun t => by ext1; exact hTT t t.2
        right_inv := fun t => by ext1; simp [wlift, Fin.init_snoc] }
    have hsum : ∑ t : T, w (e t) • (t : Fin (m+1) → ℝ) = 0 := by
      have h1 : ∑ t : T, w (e t) • (t : Fin (m+1) → ℝ) =
          ∑ t : (T.image Fin.init), w t • wlift (t : Fin m → ℝ) := by
        apply Fintype.sum_equiv e
        intro t
        simp only [e, Equiv.coe_fn_mk]
        rw [hTT t t.2]
      rw [h1]
      simp only [wlift]
      rw [wp_sum_snoc]
      have h2 : ∑ i : (T.image Fin.init), w i * (-1 : ℝ) = 0 := by
        simp only [mul_neg, mul_one, Finset.sum_neg_distrib, hw0, neg_zero]
      rw [h2, hwv, wp_snoc_zero]
    have := Fintype.linearIndependent_iff.1 hli (fun t => w (e t)) hsum
    intro i
    have := this (e.symm i)
    simpa using this
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 ht
    have := hT t0 ht0
    rw [← hTT t0 ht0, wp_dot_wlift] at this
    simpa [wlift, Fin.init_snoc] using this

lemma wp_nondeg_lift {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) (hne : S.Nonempty) :
    Shared.NonDegenerate (S.image wlift) := by
  intro α hα
  have hS' : ∀ s ∈ S, Fin.init α ⬝ᵥ s - α (Fin.last m) = 0 := by
    intro s hs
    have := hα (wlift s) (Finset.mem_image_of_mem _ hs)
    rwa [wp_dot_wlift] at this
  have hvs : vectorSpan ℝ (S : Set (Fin m → ℝ)) = ⊤ := by
    rw [← direction_affineSpan, hS, AffineSubspace.direction_top]
  have ha : Fin.init α = 0 := by
    have hmem : Fin.init α ∈ vectorSpan ℝ (S : Set (Fin m → ℝ)) := by rw [hvs]; trivial
    rw [vectorSpan_def] at hmem
    have := wp_dot_span_zero (d := Fin.init α) (T := (S : Set (Fin m → ℝ)) -ᵥ S) (by
      intro v hv
      obtain ⟨s, hs, s', hs', rfl⟩ := Set.mem_vsub.1 hv
      have h1 := hS' s hs
      have h2 := hS' s' hs'
      rw [vsub_eq_sub, dotProduct_sub]; linarith) hmem
    exact dotProduct_self_eq_zero.1 this
  obtain ⟨s, hs⟩ := hne
  have ha0 : α (Fin.last m) = 0 := by
    have := hS' s hs; rw [ha, zero_dotProduct] at this; linarith
  rw [← Fin.snoc_init_self α, ha, ha0, wp_snoc_zero]

theorem convexHull_core {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) :
    (∃ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀) ∧
      convexHull ℝ (S : Set (Fin m → ℝ)) =
        {x | ∀ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀ → 0 ≤ a ⬝ᵥ x - a₀} := by
  classical
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hS
  have hND := wp_nondeg_lift S hS hne
  constructor
  · by_contra hno
    have hno' : ¬ ∃ α, Shared.IsExtremeSupport (S.image wlift) α :=
      fun ⟨α, hα⟩ => hno ⟨_, _, wp_ext_to_affine S α hα⟩
    obtain ⟨c, hc, h0⟩ := (zusatz_core _ hND).1 hno'
    have h1 : (∑ s ∈ S.image wlift, c s • s) (Fin.last m) =
        ∑ s ∈ S.image wlift, -(c s) := by
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 ht
      simp [wlift]
    have h2 : 0 < ∑ s ∈ S.image wlift, c s := Finset.sum_pos (fun s h => hc s h) (hne.image _)
    rw [← h0, Finset.sum_neg_distrib] at h1
    simp at h1
    linarith
  · ext x
    constructor
    · intro hx
      refine convexHull_min ?_ ?_ hx
      · intro s hs a a0 h
        exact h.2.1 s hs
      · intro y hy z hz θ η hθ hη hθη a a0 h
        have h1 := hy a a0 h
        have h2 := hz a a0 h
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have : a0 = θ * a0 + η * a0 := by rw [← add_mul, hθη, one_mul]
        rw [this]; nlinarith
    · intro hx
      obtain ⟨c, hc, hrep⟩ := hauptsatz_core _ hND (wlift x) (fun α hα => by
        have := hx _ _ (wp_ext_to_affine S α hα)
        rwa [wp_dot_wlift])
      rw [Finset.sum_image (fun a _ b _ h => wlift_injective h)] at hrep
      simp only [wlift] at hrep
      rw [wp_sum_snoc] at hrep
      have hx' := congrArg Fin.init hrep
      have hl := congrFun hrep (Fin.last m)
      simp only [Fin.init_snoc, Fin.snoc_last] at hx' hl
      rw [hx']
      refine (convex_convexHull ℝ _).sum_mem (fun s hs => hc _ (Finset.mem_image_of_mem _ hs))
        ?_ (fun s hs => subset_convexHull ℝ _ hs)
      simp only [mul_neg, mul_one, Finset.sum_neg_distrib] at hl
      linarith


lemma wp_rep_fixed {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (E : Finset (Fin n → ℝ))
    (hall : ∀ α, IsExtremeSolution S α → ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧ α = c • e)
    (π : Fin n → ℝ) (hπ : π ∈ solutionRegion S) : Shared.Representable E π := by
  by_contra hnot
  obtain ⟨p, hp, hpπ⟩ := wp_farkas E π hnot
  have hdual : p ∈ dualRegion S := by
    intro α hα
    obtain ⟨e, he, c, hc, rfl⟩ := hall α hα
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]
    exact mul_nonneg hc.le (hp e he)
  have := (satz6_core S hS p).1 hdual π hπ
  linarith

lemma wp_dot_sum' {n : ℕ} {ι : Type*} (α : Fin n → ℝ) (s : Finset ι) (c : ι → ℝ)
    (f : ι → Fin n → ℝ) : α ⬝ᵥ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * (α ⬝ᵥ f i) := by
  have := map_sum (wpDotL α) (fun i => c i • f i) s
  simp only [wpDotL, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, smul_eq_mul] at this
  exact this

lemma wp_cone_zero {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (hcone : ∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j)
    (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ A j ⬝ᵥ w) : w = 0 := by
  obtain ⟨ν, hν, hπ⟩ := hcone (-w)
  have h1 : (-w) ⬝ᵥ w = ∑ j, ν j * (A j ⬝ᵥ w) := by
    rw [hπ, dotProduct_comm, wp_dot_sum']
    exact Finset.sum_congr rfl fun j _ => by rw [dotProduct_comm]
  have h2 : 0 ≤ ∑ j, ν j * (A j ⬝ᵥ w) := Finset.sum_nonneg fun j _ => mul_nonneg (hν j) (hw j)
  have h3 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [neg_dotProduct] at h1
  exact dotProduct_self_eq_zero.1 (by linarith)

lemma wp_ineq_convex {m : ℕ} {J : Type*} (A : J → Fin m → ℝ) (b : J → ℝ) :
    Convex ℝ (inequalityRegion A b) := by
  intro y hy z hz θ η hθ hη hθη j
  have h1 := hy j
  have h2 := hz j
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have : b j = θ * b j + η * b j := by rw [← add_mul, hθη, one_mul]
  rw [this]; nlinarith

theorem goal_core {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (b : J → ℝ) (hrow : ∀ j, A j ≠ 0 ∨ b j ≠ 0) :
    IsConvexPolyhedron (inequalityRegion A b) ↔
      ((∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j) ∧
        ∃ c : Fin m → ℝ, ∀ j, 0 < A j ⬝ᵥ c - b j) := by
  classical
  have hUopen : IsOpen {x : Fin m → ℝ | ∀ j, 0 < A j ⬝ᵥ x - b j} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
      ((Continuous.dotProduct continuous_const continuous_id).sub continuous_const)
  have hUH : {x : Fin m → ℝ | ∀ j, 0 < A j ⬝ᵥ x - b j} ⊆ inequalityRegion A b :=
    fun x hx j => (hx j).le
  constructor
  · rintro ⟨S, hS, hH⟩
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hS
    obtain ⟨c, hcint⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.2 hS
    rw [← hH] at hcint
    have hcH : c ∈ inequalityRegion A b := interior_subset hcint
    have hstrict : ∀ j, 0 < A j ⬝ᵥ c - b j := by
      intro j
      rcases (hcH j).lt_or_eq with h | h
      · exact h
      exfalso
      by_cases hA : A j = 0
      · rw [hA, zero_dotProduct] at h
        rcases hrow j with h' | h'
        · exact h' hA
        · exact h' (by linarith)
      · have hnhds : inequalityRegion A b ∈ nhds c := mem_interior_iff_mem_nhds.1 hcint
        let f : ℝ → Fin m → ℝ := fun t => c - t • A j
        have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
        have hpre : f ⁻¹' inequalityRegion A b ∈ nhds (0 : ℝ) :=
          hf.continuousAt.preimage_mem_nhds (by simpa [f] using hnhds)
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
        have hmem : f (ε / 2) ∈ inequalityRegion A b := hball (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
        have h1 := hmem j
        simp only [f, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
        have hpos : 0 < A j ⬝ᵥ A j := by
          rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (A j i)) :
            (0 : ℝ) ≤ A j ⬝ᵥ A j).lt_or_eq with h2 | h2
          · exact h2
          · exact absurd (dotProduct_self_eq_zero.1 h2.symm) hA
        nlinarith
    refine ⟨?_, c, hstrict⟩
    intro π'
    by_contra hno
    set Ahat := Finset.univ.image A with hAhat
    have hnrep : ¬ Shared.Representable Ahat π' := by
      rintro ⟨cc, hcc, hπ⟩
      apply hno
      let ν : J → ℝ := fun j => cc (A j) / ((Finset.univ.filter fun j' => A j' = A j).card : ℝ)
      refine ⟨ν, fun j => div_nonneg (hcc _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
        (Nat.cast_nonneg _), ?_⟩
      rw [hπ, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Ahat) (g := A)
        (fun j _ => Finset.mem_image_of_mem _ (Finset.mem_univ j))]
      apply Finset.sum_congr rfl
      intro a ha
      have hk : 0 < (Finset.univ.filter fun j' => A j' = a).card := by
        obtain ⟨j, _, hj⟩ := Finset.mem_image.1 ha
        exact Finset.card_pos.2 ⟨j, by simp [hj]⟩
      rw [Finset.sum_congr rfl (g := fun _ => (cc a /
        ((Finset.univ.filter fun j' => A j' = a).card : ℝ)) • a) (fun j hj => by
          have := (Finset.mem_filter.1 hj).2
          simp only [ν, this])]
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        mul_div_cancel₀ _ (ne_of_gt (Nat.cast_pos.2 hk))]
    obtain ⟨p, hp, hpπ⟩ := wp_farkas Ahat π' hnrep
    set M : ℝ := ∑ s ∈ S, |π' ⬝ᵥ s| with hM
    have hbound : ∀ x ∈ inequalityRegion A b, -M ≤ π' ⬝ᵥ x := by
      intro x hx
      rw [hH] at hx
      suffices h : x ∈ {y : Fin m → ℝ | -M ≤ π' ⬝ᵥ y} from h
      refine convexHull_min ?_ ?_ hx
      · intro s hs
        have h1 : |π' ⬝ᵥ s| ≤ M := Finset.single_le_sum (f := fun s => |π' ⬝ᵥ s|)
          (fun _ _ => abs_nonneg _) hs
        have h2 := neg_abs_le (π' ⬝ᵥ s)
        show -M ≤ π' ⬝ᵥ s
        linarith
      · intro y hy z hz θ η hθ hη hθη
        show -M ≤ π' ⬝ᵥ (θ • y + η • z)
        have h1 : -M ≤ π' ⬝ᵥ y := hy
        have h2 : -M ≤ π' ⬝ᵥ z := hz
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have : -M = θ * (-M) + η * (-M) := by rw [← add_mul, hθη, one_mul]
        rw [this]; nlinarith
    have hpπ' : π' ⬝ᵥ p < 0 := by rw [dotProduct_comm]; exact hpπ
    set t : ℝ := (|π' ⬝ᵥ c| + M + 1) / (-(π' ⬝ᵥ p)) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hmem : c + t • p ∈ inequalityRegion A b := by
      intro j
      have h1 := hcH j
      have h2 := hp (A j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm (A j) p]
      nlinarith
    have h1 := hbound _ hmem
    have htq : t * (π' ⬝ᵥ p) = -(|π' ⬝ᵥ c| + M + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, htq] at h1
    have h2 := le_abs_self (π' ⬝ᵥ c)
    linarith
  · rintro ⟨hcone, c, hc⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨{0}, ?_, ?_⟩
      · rw [eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 0]
        exact subset_affineSpan ℝ _ (by simp)
      · ext x
        rw [Finset.coe_singleton, convexHull_singleton]
        simp only [Set.mem_singleton_iff, Subsingleton.elim x 0, iff_true]
        rw [Subsingleton.elim (0 : Fin 0 → ℝ) c]
        exact fun j => (hc j).le
    obtain ⟨j0⟩ : Nonempty J := by
      by_contra hJ
      rw [not_nonempty_iff] at hJ
      obtain ⟨ν, _, hν⟩ := hcone (Pi.single ⟨0, hm⟩ 1)
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hν
      have := congrFun hν ⟨0, hm⟩
      simp at this
    let rowv : J → Fin (m+1) → ℝ := fun j => Fin.snoc (A j) (b j)
    set Shat := Finset.univ.image rowv with hShat
    -- every nonzero point of the homogenized region has negative last coordinate
    have hlast : ∀ ξ ∈ solutionRegion Shat, ξ ≠ 0 → ξ (Fin.last m) < 0 := by
      intro ξ hξ hξ0
      by_contra hz
      push_neg at hz
      have hj : ∀ j, 0 ≤ A j ⬝ᵥ Fin.init ξ + b j * ξ (Fin.last m) := by
        intro j
        have := hξ (rowv j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        rwa [← Fin.snoc_init_self ξ, wp_dot_snoc] at this
      set z := ξ (Fin.last m)
      set w := Fin.init ξ + z • c with hw
      have hAw : ∀ j, z * (A j ⬝ᵥ c - b j) ≤ A j ⬝ᵥ w := by
        intro j
        rw [hw, dotProduct_add, dotProduct_smul, smul_eq_mul]
        have := hj j; nlinarith
      have hw0 : w = 0 := wp_cone_zero A hcone w fun j =>
        le_trans (mul_nonneg hz (hc j).le) (hAw j)
      rcases hz.lt_or_eq with hz' | hz'
      · have := hAw j0
        rw [hw0, dotProduct_zero] at this
        have := mul_pos hz' (hc j0)
        linarith
      · apply hξ0
        have hy : Fin.init ξ = 0 := by
          rw [hw, ← hz', zero_smul, add_zero] at hw0; exact hw0
        rw [← Fin.snoc_init_self ξ, hy, show ξ (Fin.last m) = 0 from hz'.symm, wp_snoc_zero]
    have hND : Shared.NonDegenerate Shat := by
      intro p hp
      have hj : ∀ j, A j ⬝ᵥ Fin.init p + b j * p (Fin.last m) = 0 := by
        intro j
        have := hp (rowv j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        rwa [dotProduct_comm, ← Fin.snoc_init_self p, wp_dot_snoc] at this
      set z := p (Fin.last m)
      set w := Fin.init p + z • c with hw
      have hAw : ∀ j, A j ⬝ᵥ w = z * (A j ⬝ᵥ c - b j) := by
        intro j
        rw [hw, dotProduct_add, dotProduct_smul, smul_eq_mul]
        have := hj j; linarith
      rcases lt_trichotomy z 0 with hz | hz | hz
      · exfalso
        have hw0 : -w = 0 := wp_cone_zero A hcone (-w) fun j => by
          rw [dotProduct_neg, hAw j]; have := hc j; nlinarith
        have := hAw j0
        rw [neg_eq_zero.1 hw0, dotProduct_zero] at this
        have := mul_neg_of_neg_of_pos hz (hc j0)
        linarith
      · have hy : Fin.init p = 0 := wp_cone_zero A hcone _ fun j => by
          have := hj j; rw [hz, mul_zero, add_zero] at this; rw [this]
        rw [← Fin.snoc_init_self p, hy, show p (Fin.last m) = 0 from hz, wp_snoc_zero]
      · exfalso
        have hw0 : w = 0 := wp_cone_zero A hcone w fun j => by
          rw [hAw j]; have := hc j; nlinarith
        have := hAw j0
        rw [hw0, dotProduct_zero] at this
        have := mul_pos hz (hc j0)
        linarith
    obtain ⟨E, hE, hall⟩ := wp_finite_extreme Shat hND
    have hElast : ∀ e ∈ E, e (Fin.last m) < 0 := fun e he => hlast e (hE e he).1 (hE e he).2.1
    let pt : (Fin (m+1) → ℝ) → Fin m → ℝ := fun e => (-(e (Fin.last m)))⁻¹ • Fin.init e
    have hSH : ((E.image pt : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) ⊆ inequalityRegion A b := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      intro j
      have h1 := (hE e he).1 (rowv j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      rw [← Fin.snoc_init_self e, wp_dot_snoc] at h1
      have hz := hElast e he
      have hz0 : e (Fin.last m) ≠ 0 := hz.ne
      simp only [pt, dotProduct_smul, smul_eq_mul]
      have : (-(e (Fin.last m)))⁻¹ * (A j ⬝ᵥ Fin.init e) - b j =
          (-(e (Fin.last m)))⁻¹ * (A j ⬝ᵥ Fin.init e + b j * e (Fin.last m)) := by
        field_simp; ring
      rw [this]
      exact mul_nonneg (inv_nonneg.2 (by linarith)) h1
    have hHS : inequalityRegion A b ⊆
        convexHull ℝ ((E.image pt : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
      intro x hx
      have hsol : wlift x ∈ solutionRegion Shat := by
        intro a ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 ha
        simp only [rowv, wlift]
        rw [wp_dot_snoc]
        have := hx j
        linarith
      obtain ⟨l, hl, hrep⟩ := wp_rep_fixed Shat hND E hall _ hsol
      have hrep' : wlift x = Fin.snoc (∑ e ∈ E, l e • Fin.init e)
          (∑ e ∈ E, l e * e (Fin.last m)) := by
        rw [hrep, ← wp_sum_snoc]
        exact Finset.sum_congr rfl fun e _ => by rw [Fin.snoc_init_self]
      have hx' := congrArg Fin.init hrep'
      have hl' := congrFun hrep' (Fin.last m)
      simp only [wlift, Fin.init_snoc, Fin.snoc_last] at hx' hl'
      have heq : ∑ e ∈ E, l e • Fin.init e =
          ∑ e ∈ E, (l e * (-(e (Fin.last m)))) • pt e := by
        apply Finset.sum_congr rfl
        intro e he
        have hz := (hElast e he).ne
        simp only [pt, smul_smul]
        congr 1
        field_simp
      rw [hx', heq]
      refine (convex_convexHull ℝ _).sum_mem
        (fun e he => mul_nonneg (hl e he) (by linarith [hElast e he])) ?_
        (fun e he => subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ he)))
      simp only [mul_neg, Finset.sum_neg_distrib]
      linarith
    have hEq : inequalityRegion A b =
        convexHull ℝ ((E.image pt : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
      Set.Subset.antisymm hHS (convexHull_min hSH (wp_ineq_convex A b))
    refine ⟨E.image pt, ?_, hEq⟩
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.1
    rw [← hEq]
    exact ⟨c, interior_maximal hUH hUopen (show c ∈ {x : Fin m → ℝ | ∀ j, 0 < A j ⬝ᵥ x - b j} from hc)⟩

end WeylPolyhedra.Polyhedron

open WeylPolyhedra.Polyhedron
open WeylPolyhedra

theorem solution {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (b : J → ℝ) (hrow : ∀ j, A j ≠ 0 ∨ b j ≠ 0) :
    IsConvexPolyhedron (inequalityRegion A b) ↔
      ((∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j) ∧
        ∃ c : Fin m → ℝ, ∀ j, 0 < A j ⬝ᵥ c - b j) := by
  exact goal_core A b hrow
