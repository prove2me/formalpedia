-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.satz9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:02:55.622261+00:00
-- url     : https://prove2.me/submissions/a90b4cea-da13-4b5c-a64c-2ac55deb4eec

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

end WeylPolyhedra.Polyhedron

open WeylPolyhedra.Polyhedron
open WeylPolyhedra

theorem solution {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ p : Fin n → ℝ, (∀ α : Fin n → ℝ, IsExtremeSolution S α → α ⬝ᵥ p = 0) → p = 0 := by
  exact satz9_core S hS hint
