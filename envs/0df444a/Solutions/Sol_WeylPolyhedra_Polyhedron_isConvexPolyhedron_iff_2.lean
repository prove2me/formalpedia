-- Prove2me | solution 2 for WeylPolyhedra.Polyhedron.isConvexPolyhedron_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:43:00.704389+00:00
-- url     : https://prove2.me/submissions/1769a744-8417-4a16-9b2a-577f0288e668

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope
import Theorems.Thm_WeylPolyhedra_Pyramid_hauptsatz

-- carved verbatim out of submission f32d88fc-31c2-416b-b0c3-18f638f48cb6, lines 937-943

section
open WeylPolyhedra
open WeylPolyhedra.Polyhedron
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

lemma wp_dot_sum {n : ℕ} (α : Fin n → ℝ) (S : Finset (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ) :
    α ⬝ᵥ (∑ s ∈ S, c s • s) = ∑ s ∈ S, c s * (α ⬝ᵥ s) := by
  have := map_sum (wpDotL α) (fun s => c s • s) S
  simp only [wpDotL, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, smul_eq_mul] at this
  exact this

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
    obtain ⟨c, hc, rfl⟩ := WeylPolyhedra.Pyramid.hauptsatz S hS p
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

def wlift {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.snoc x (-1)

lemma wp_dot_snoc {m : ℕ} (a x : Fin m → ℝ) (a0 y : ℝ) :
    (Fin.snoc a a0 : Fin (m+1) → ℝ) ⬝ᵥ (Fin.snoc x y : Fin (m+1) → ℝ) = a ⬝ᵥ x + a0 * y := by
  simp [dotProduct, Fin.sum_univ_castSucc]

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

end

section
open WeylPolyhedra.Polyhedron
open WeylPolyhedra

theorem solution {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (b : J → ℝ) (hrow : ∀ j, A j ≠ 0 ∨ b j ≠ 0) :
    IsConvexPolyhedron (inequalityRegion A b) ↔
      ((∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j) ∧
        ∃ c : Fin m → ℝ, ∀ j, 0 < A j ⬝ᵥ c - b j) := by
  exact goal_core A b hrow

end
