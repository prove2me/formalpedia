-- Prove2me | solution 1 for PhiDivRobust.Counterpart.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:22:01.738684+00:00
-- url     : https://prove2.me/submissions/a0eca55c-f95b-4f44-a583-c285f7611842

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix


namespace PhiDivRobust.Counterpart

namespace SDLP
set_option linter.unusedSectionVars false
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def PFeas (M : Matrix κ ι ℝ) (r : κ → ℝ) (z : ι → ℝ) : Prop := (∀ j, 0 ≤ z j) ∧ M *ᵥ z = r

noncomputable def supp (z : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)

def ColLI (M : Matrix κ ι ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ (fun j : S => Mᵀ (j : ι))

lemma mem_supp {z : ι → ℝ} {j : ι} : j ∈ supp z ↔ z j ≠ 0 := by simp [supp]

lemma sum_sub_eq_mulVec (M : Matrix κ ι ℝ) (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ j, j ∉ S → w j = 0) :
    ∑ j : S, w j • Mᵀ (j : ι) = M *ᵥ w := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => w j * M i j)]
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro j _ hj; simp [hw j hj]

lemma reduce (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) :
    ∀ n, ∀ z, (supp z).card = n → PFeas M r z →
      ∃ z', PFeas M r z' ∧ c ⬝ᵥ z' ≤ c ⬝ᵥ z ∧ supp z' ⊆ supp z ∧ ColLI M (supp z') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  by_cases hli : ColLI M (supp z)
  · exact ⟨z, hz, le_rfl, subset_rfl, hli⟩
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let d : ι → ℝ := fun j => if h : j ∈ supp z then g ⟨j, h⟩ else 0
  have hdS : ∀ j, j ∉ supp z → d j = 0 := by intro j hj; simp [d, hj]
  have hMd : M *ᵥ d = 0 := by
    rw [← sum_sub_eq_mulVec M (supp z) d hdS]
    convert hg using 2 with j
    simp [d]
  have hdi0 : d i0 ≠ 0 := by simpa [d] using hi0
  have hzpos : ∀ j, 0 ≤ z j := hz.1
  -- unboundedness contradiction
  have unb : ∀ e : ι → ℝ, M *ᵥ e = 0 → (∀ j, 0 ≤ e j) → c ⬝ᵥ e < 0 → False := by
    intro e hMe he hce
    set s := (c ⬝ᵥ z - L + 1) / (-(c ⬝ᵥ e)) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hL z hz]) (by linarith)
    have hf : PFeas M r (z + s • e) := ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hzpos j) (mul_nonneg hs0 (he j)), by
      rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    have := hL _ hf
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hse : s * (c ⬝ᵥ e) = -(c ⬝ᵥ z - L + 1) := by
      have hne : -(c ⬝ᵥ e) ≠ 0 := by linarith
      have h2 : (c ⬝ᵥ z - L + 1) / -(c ⬝ᵥ e) * -(c ⬝ᵥ e) = c ⬝ᵥ z - L + 1 := div_mul_cancel₀ _ hne
      rw [hs]; linear_combination -h2
    linarith
  obtain ⟨e, hMe, heS, hce, j0, hj0⟩ : ∃ e : ι → ℝ, M *ᵥ e = 0 ∧ (∀ j, j ∉ supp z → e j = 0) ∧
      c ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
    obtain ⟨d1, hMd1, hd1S, hcd1, hd1i0⟩ : ∃ d1 : ι → ℝ, M *ᵥ d1 = 0 ∧
        (∀ j, j ∉ supp z → d1 j = 0) ∧ c ⬝ᵥ d1 ≤ 0 ∧ d1 i0 ≠ 0 := by
      by_cases h : c ⬝ᵥ d ≤ 0
      · exact ⟨d, hMd, hdS, h, hdi0⟩
      · refine ⟨-d, by rw [mulVec_neg, hMd, neg_zero], fun j hj => by simp [hdS j hj], ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · simpa using hdi0
    by_cases hneg : ∃ j, d1 j < 0
    · exact ⟨d1, hMd1, hd1S, hcd1, hneg⟩
    push_neg at hneg
    rcases hcd1.lt_or_eq with hlt | heq
    · exact (unb d1 hMd1 hneg hlt).elim
    · refine ⟨-d1, by rw [mulVec_neg, hMd1, neg_zero], fun j hj => by simp [hd1S j hj],
        by rw [dotProduct_neg, heq, neg_zero], i0, ?_⟩
      have := lt_of_le_of_ne (hneg i0) (Ne.symm hd1i0)
      simp only [Pi.neg_apply]; linarith
  let P := Finset.univ.filter (fun j => e j < 0)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => z j / (-e j)) ⟨j0, by simp [P, hj0]⟩
  have hejm : e jm < 0 := by simpa [P] using hjmP
  set t := z jm / (-e jm) with ht
  have ht0 : 0 ≤ t := div_nonneg (hzpos jm) (by linarith)
  let z' := z + t • e
  have hz' : PFeas M r z' := by
    refine ⟨fun j => ?_, by simp only [z']; rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hej : e j < 0
    · have h1 : t ≤ z j / (-e j) := hjm j (by simp [P, hej])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push_neg at hej
      exact add_nonneg (hzpos j) (mul_nonneg ht0 hej)
  have hsub : supp z' ⊆ supp z := by
    intro j hj
    rw [mem_supp] at hj ⊢
    intro hzj
    apply hj
    have : e j = 0 := by
      by_contra hne
      exact absurd (heS j) (by
        intro h'
        have : j ∉ supp z := by rw [mem_supp]; exact fun h => h hzj
        exact hne (h' this))
    simp [z', hzj, this]
  have hjm_in : jm ∈ supp z := by
    by_contra h; exact absurd (heS jm h) (ne_of_lt hejm)
  have hjm_out : jm ∉ supp z' := by
    rw [mem_supp, not_not]
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
    have hne : e jm ≠ 0 := ne_of_lt hejm
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  have hlt : (supp z').card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨hsub, fun h => hjm_out (h hjm_in)⟩
  obtain ⟨z'', h1, h2, h3, h4⟩ := ih _ hlt z' rfl hz'
  refine ⟨z'', h1, le_trans h2 ?_, h3.trans hsub, h4⟩
  simp only [z', dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith

lemma colLI_unique (M : Matrix κ ι ℝ) (z1 z2 : ι → ℝ) (h : supp z1 = supp z2)
    (hli : ColLI M (supp z1)) (hM : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have hw : ∀ j, j ∉ supp z1 → (z1 - z2) j = 0 := by
    intro j hj
    have hj2 : j ∉ supp z2 := h ▸ hj
    rw [mem_supp, not_not] at hj hj2
    simp [hj, hj2]
  have hsum := sum_sub_eq_mulVec M (supp z1) (z1 - z2) hw
  rw [mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (z1 - z2) j) hsum
  funext j
  by_cases hj : j ∈ supp z1
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma attain (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ zs, PFeas M r zs ∧ ColLI M (supp zs) ∧ ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z := by
  let F : Set (ι → ℝ) := {z | PFeas M r z ∧ ColLI M (supp z)}
  have hinj : Set.InjOn supp F := by
    intro z1 h1 z2 h2 h
    exact colLI_unique M z1 z2 h h1.2 (by rw [h1.1.2, h2.1.2])
  have hfin : F.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  obtain ⟨z1, hz1, _, _, hz1li⟩ := reduce M r c L hL _ z0 rfl hz0
  obtain ⟨zs, hzs, hmin⟩ := Set.exists_min_image F (fun z => c ⬝ᵥ z) hfin ⟨z1, hz1, hz1li⟩
  refine ⟨zs, hzs.1, hzs.2, fun z hz => ?_⟩
  obtain ⟨z', hz', hc', _, hli'⟩ := reduce M r c L hL _ z rfl hz
  exact le_trans (hmin z' ⟨hz', hli'⟩) hc'


def cone (M : Matrix κ ι ℝ) : Set (κ → ℝ) := (M.mulVecLin) '' {z | ∀ j, 0 ≤ z j}

lemma cone_closed (M : Matrix κ ι ℝ) : IsClosed (cone M) := by
  have heq : cone M = ⋃ (S : Finset ι) (_ : ColLI M S),
      (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) '' {w | ∀ j, 0 ≤ w j} := by
    ext t
    simp only [cone, Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion, mulVecLin_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨z', hz', _, _, hli⟩ := reduce M (M *ᵥ z) 0 0 (fun _ _ => by simp) _ z rfl ⟨hz, rfl⟩
      refine ⟨supp z', hli, fun j => z' j, fun j => hz'.1 j, ?_⟩
      rw [Fintype.linearCombination_apply, sum_sub_eq_mulVec M (supp z') z'
        (fun j hj => by rw [mem_supp, not_not] at hj; exact hj), hz'.2]
    · rintro ⟨S, _, w, hw, rfl⟩
      refine ⟨fun j => if h : j ∈ S then w ⟨j, h⟩ else 0, fun j => ?_, ?_⟩
      · by_cases h : j ∈ S <;> simp [h, hw]
      · rw [Fintype.linearCombination_apply, ← sum_sub_eq_mulVec M S _ (fun j hj => by simp [hj])]
        simp
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro S
  apply isClosed_iUnion_of_finite
  intro hli
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  apply (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap
  have : {w : S → ℝ | ∀ j, 0 ≤ w j} = ⋂ j, {w | 0 ≤ w j} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))

lemma farkas (M : Matrix κ ι ℝ) (t : κ → ℝ) (ht : t ∉ cone M) :
    ∃ y : κ → ℝ, (∀ j, 0 ≤ (y ᵥ* M) j) ∧ y ⬝ᵥ t < 0 := by
  have hconv : Convex ℝ (cone M) := by
    apply Convex.linear_image
    have : {z : ι → ℝ | ∀ j, 0 ≤ z j} = Set.Ici 0 := by ext; simp [Pi.le_def]
    rw [this]; exact convex_Ici 0
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hconv (cone_closed M) ht
  have h0 : 0 < u := by
    have := hfu 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hneg : ∀ a ∈ cone M, f a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨z, hz, rfl⟩ := ha
    have hs : 0 ≤ u / f (M.mulVecLin z) + 1 := by positivity
    have hmem : (u / f (M.mulVecLin z) + 1) • M.mulVecLin z ∈ cone M :=
      ⟨(u / f (M.mulVecLin z) + 1) • z, fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs (hz j), by simp⟩
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt h)] at this
    linarith
  have hf : ∀ v : κ → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
    simpa using this
  refine ⟨fun i => - f (fun j => if i = j then 1 else 0), fun j => ?_, ?_⟩
  · have hmem : Mᵀ j ∈ cone M := ⟨Pi.single j 1, fun k => by
      by_cases h : k = j
      · subst h; simp
      · simp [h], by ext i; simp [mulVec, dotProduct, Pi.single_apply]⟩
    have := hneg _ hmem
    rw [hf] at this
    simp only [vecMul, dotProduct, transpose_apply] at this ⊢
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * M x j =
        -∑ x, M x j * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  · have := hf t
    simp only [dotProduct]
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * t x =
        -∑ x, t x * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith


end SDLP

open SDLP in
theorem sd_lp_dual {m k : ℕ} (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ) (g : Fin m → ℝ)
    (s : ℝ) (p0 : Fin m → ℝ) (hp0 : C *ᵥ p0 ≤ d) (h : ∀ p, C *ᵥ p ≤ d → s ≤ g ⬝ᵥ p) :
    ∃ η : Fin k → ℝ, 0 ≤ η ∧ η ᵥ* C = -g ∧ η ⬝ᵥ d ≤ -s := by
  classical
  let M' : Matrix (Option (Fin m)) (Option (Fin k)) ℝ := fun o o' => match o, o' with
    | none, none => 1
    | none, some j => d j
    | some _, none => 0
    | some i, some j => C j i
  let t' : Option (Fin m) → ℝ := fun o => match o with
    | none => -s
    | some i => -g i
  by_cases hmem : t' ∈ cone M'
  · obtain ⟨z, hz, hMz⟩ := hmem
    simp only [mulVecLin_apply] at hMz
    refine ⟨fun j => z (some j), fun j => hz _, ?_, ?_⟩
    · funext i
      have := congrFun hMz (some i)
      simpa [M', t', mulVec, dotProduct, Fintype.sum_option, vecMul, mul_comm] using this
    · have := congrFun hMz none
      simp [M', t', mulVec, dotProduct, Fintype.sum_option] at this
      have h0 := hz none
      simp only [dotProduct]
      have : ∑ x, z (some x) * d x = ∑ x, d x * z (some x) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      linarith
  · obtain ⟨y, hy, hyt⟩ := farkas M' t' hmem
    set ω := y none
    let w : Fin m → ℝ := fun i => y (some i)
    have hω : 0 ≤ ω := by
      have := hy none
      simpa [M', vecMul, dotProduct, Fintype.sum_option] using this
    have hcol : ∀ j, 0 ≤ (C *ᵥ w) j + ω * d j := by
      intro j
      have := hy (some j)
      simp [M', vecMul, dotProduct, Fintype.sum_option, w, mulVec] at this ⊢
      have e : ∑ x, C j x * y (some x) = ∑ x, y (some x) * C j x :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      linarith
    have hyt' : -(w ⬝ᵥ g) - ω * s < 0 := by
      simp [t', dotProduct, Fintype.sum_option, w] at hyt ⊢
      linarith
    rcases hω.lt_or_eq with hωp | hω0
    · exfalso
      have hp : C *ᵥ ((-ω⁻¹) • w) ≤ d := by
        intro j
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have := hcol j
        have h1 : -ω⁻¹ * (C *ᵥ w) j = -((C *ᵥ w) j / ω) := by field_simp
        rw [h1, neg_le, le_div_iff₀ hωp] at *
        nlinarith
      have := h _ hp
      rw [dotProduct_smul, smul_eq_mul, dotProduct_comm] at this
      have h2 : ω * s ≤ ω * (-ω⁻¹ * (w ⬝ᵥ g)) := mul_le_mul_of_nonneg_left this hωp.le
      have h3 : ω * (-ω⁻¹ * (w ⬝ᵥ g)) = -(w ⬝ᵥ g) := by field_simp
      linarith
    · exfalso
      rw [← hω0] at hcol hyt'
      have hwg : 0 < w ⬝ᵥ g := by linarith
      set τ := (g ⬝ᵥ p0 - s + 1) / (w ⬝ᵥ g) with hτ
      have hτ0 : 0 ≤ τ := by
        have := h p0 hp0
        exact div_nonneg (by linarith) hwg.le
      have hp : C *ᵥ (p0 - τ • w) ≤ d := by
        intro j
        rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have := hcol j
        have := hp0 j
        nlinarith
      have := h _ hp
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm g w] at this
      have : τ * (w ⬝ᵥ g) = g ⬝ᵥ p0 - s + 1 := by
        rw [hτ]; field_simp
      linarith


theorem sd_le_of_eps {X K : ℝ} (hK : 0 ≤ K) (h : ∀ ε : ℝ, 0 < ε → X < ε * K) : X ≤ 0 := by
  by_contra hX
  push_neg at hX
  have h1 := h (X / (K + 1)) (div_pos hX (by linarith))
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)] at h1
  nlinarith

theorem sd_le_of_theta {X Y : ℝ} (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → X ≤ θ * Y) : X ≤ 0 := by
  by_cases hY : Y ≤ 0
  · have := h 1 one_pos le_rfl; linarith
  · push_neg at hY
    by_contra hX
    push_neg at hX
    have h1 := h (min 1 (X / (2 * Y))) (lt_min one_pos (by positivity)) (min_le_left _ _)
    have h2 : min 1 (X / (2 * Y)) * Y ≤ X / (2 * Y) * Y :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hY.le
    have h3 : X / (2 * Y) * Y = X / 2 := by field_simp
    linarith

theorem sd_comb_pos {a b x1 x2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h1 : 0 < x1) (h2 : 0 < x2) : 0 < a * x1 + b * x2 := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have : b = 1 := by linarith
    subst this; linarith
  · nlinarith [mul_pos h h1, mul_nonneg hb h2.le]

/-- Step D: one-constraint Lagrange multiplier under Slater. -/
theorem sd_stepD {m : ℕ} (O : Set (Fin m → ℝ)) (hO : Convex ℝ O) (Dr : (Fin m → ℝ) → ℝ)
    (hD : ConvexOn ℝ O Dr) (q : Fin m → ℝ) (hqO : q ∈ O) (ρ : ℝ) (hDq : Dr q < ρ)
    (w : Fin m → ℝ) (κ0 : ℝ) (h : ∀ p ∈ O, Dr p < ρ → w ⬝ᵥ p + κ0 ≤ 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ p ∈ O, w ⬝ᵥ p + κ0 ≤ lam * (Dr p - ρ) := by
  let A2 : Set (ℝ × ℝ) := {z | ∃ p ∈ O, Dr p - ρ < z.1 ∧ z.2 < w ⬝ᵥ p + κ0}
  let B2 : Set (ℝ × ℝ) := {z | z.1 ≤ 0 ∧ 0 ≤ z.2}
  have hA2c : Convex ℝ A2 := by
    rintro z1 ⟨p1, hp1, h11, h12⟩ z2 ⟨p2, hp2, h21, h22⟩ a b ha hb hab
    refine ⟨a • p1 + b • p2, hO hp1 hp2 ha hb hab, ?_, ?_⟩
    · have := hD.2 hp1 hp2 ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have := sd_comb_pos ha hb hab (sub_pos.2 h11) (sub_pos.2 h21)
      have e : a * ρ + b * ρ = ρ := by rw [← add_mul, hab, one_mul]
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, dotProduct_add, dotProduct_smul]
      have := sd_comb_pos ha hb hab (sub_pos.2 h12) (sub_pos.2 h22)
      have e : a * κ0 + b * κ0 = κ0 := by rw [← add_mul, hab, one_mul]
      nlinarith
  have hB2c : Convex ℝ B2 := by
    rintro z1 ⟨h11, h12⟩ z2 ⟨h21, h22⟩ a b ha hb hab
    simp only [B2, Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add,
      Prod.smul_snd]
    constructor <;> nlinarith
  have hA2o : IsOpen A2 := by
    have : A2 = ⋃ p ∈ O, ({z : ℝ × ℝ | Dr p - ρ < z.1} ∩ {z | z.2 < w ⬝ᵥ p + κ0}) := by
      ext z; simp only [A2, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    rw [this]
    exact isOpen_biUnion fun p _ =>
      (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_snd continuous_const)
  have hdisj : Disjoint A2 B2 := by
    rw [Set.disjoint_left]
    rintro z ⟨p, hp, h1, h2⟩ ⟨h3, h4⟩
    have := h p hp (by linarith)
    linarith
  obtain ⟨f, u, hA, hB⟩ := geometric_hahn_banach_open hA2c hA2o hB2c hdisj
  have hf : ∀ v t : ℝ, f (v, t) = v * f (1, 0) + t * f (0, 1) := by
    intro v t
    have : ((v, t) : ℝ × ℝ) = v • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  set α := f (1, 0)
  set μ := f (0, 1)
  have hu0 : u ≤ 0 := by
    have := hB (0, 0) ⟨le_rfl, le_rfl⟩
    rw [hf] at this; linarith
  have hα : α ≤ 0 := by
    by_contra hα; push_neg at hα
    have := hB ((u - 1) / α, 0) ⟨div_nonpos_of_nonpos_of_nonneg (by linarith) hα.le, le_rfl⟩
    rw [hf, div_mul_cancel₀ _ hα.ne'] at this; linarith
  have hμ : 0 ≤ μ := by
    by_contra hμ; push_neg at hμ
    have := hB (0, (u - 1) / μ) ⟨le_rfl, div_nonneg_of_nonpos (by linarith) hμ.le⟩
    rw [hf, div_mul_cancel₀ _ hμ.ne] at this; linarith
  have hmain : ∀ p ∈ O, ∀ ε : ℝ, 0 < ε →
      (Dr p - ρ + ε) * α + (w ⬝ᵥ p + κ0 - ε) * μ < 0 := by
    intro p hp ε hε
    have := hA (Dr p - ρ + ε, w ⬝ᵥ p + κ0 - ε) ⟨p, hp, by simp; linarith, by simp; linarith⟩
    rw [hf] at this; linarith
  have hμp : 0 < μ := by
    rcases hμ.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have := hmain q hqO ((ρ - Dr q) / 2) (by linarith)
      rw [← h1] at this
      nlinarith
  refine ⟨-α / μ, div_nonneg (by linarith) hμp.le, fun p hp => ?_⟩
  have key : (Dr p - ρ) * α + (w ⬝ᵥ p + κ0) * μ ≤ 0 := by
    apply sd_le_of_eps (K := μ - α) (by linarith)
    intro ε hε
    have := hmain p hp ε hε
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hμp]
  linarith


/-- Steps A+B: separation plus LP duality for the linear constraints. -/
theorem sd_stepA {m k : ℕ} (O : Set (Fin m → ℝ)) (hOo : IsOpen O) (hO : Convex ℝ O)
    (Dr : (Fin m → ℝ) → ℝ) (hD : ConvexOn ℝ O Dr) (q : Fin m → ℝ) (hqO : q ∈ O) (ρ : ℝ)
    (hDq : Dr q < ρ) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ) (hCq : C *ᵥ q ≤ d)
    (c : Fin m → ℝ) (γ : ℝ) (h : ∀ p ∈ O, Dr p < ρ → C *ᵥ p ≤ d → c ⬝ᵥ p ≤ γ) :
    ∃ η : Fin k → ℝ, 0 ≤ η ∧ ∀ p ∈ O, Dr p < ρ → c ⬝ᵥ p + η ⬝ᵥ (d - C *ᵥ p) ≤ γ := by
  have hcont : ContinuousOn Dr O := hD.continuousOn hOo
  let A : Set ((Fin m → ℝ) × ℝ) := {z | z.1 ∈ O ∧ Dr z.1 < ρ ∧ z.2 < c ⬝ᵥ z.1 - γ}
  let B : Set ((Fin m → ℝ) × ℝ) := {z | C *ᵥ z.1 ≤ d ∧ 0 ≤ z.2}
  have hAo : IsOpen A := by
    have h1 : IsOpen (O ∩ Dr ⁻¹' Set.Iio ρ) := hcont.isOpen_inter_preimage hOo isOpen_Iio
    have h2 : IsOpen {z : (Fin m → ℝ) × ℝ | z.2 < c ⬝ᵥ z.1 - γ} := by
      apply isOpen_lt continuous_snd
      simp only [dotProduct]
      fun_prop
    have : A = (Prod.fst ⁻¹' (O ∩ Dr ⁻¹' Set.Iio ρ)) ∩ {z | z.2 < c ⬝ᵥ z.1 - γ} := by
      ext z; simp [A, and_assoc]
    rw [this]
    exact (h1.preimage continuous_fst).inter h2
  have hAc : Convex ℝ A := by
    rintro z1 ⟨h11, h12, h13⟩ z2 ⟨h21, h22, h23⟩ a b ha hb hab
    refine ⟨hO h11 h21 ha hb hab, ?_, ?_⟩
    · have := hD.2 h11 h21 ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.fst_add, Prod.smul_fst]
      have := sd_comb_pos ha hb hab (sub_pos.2 h12) (sub_pos.2 h22)
      have e : a * ρ + b * ρ = ρ := by rw [← add_mul, hab, one_mul]
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        dotProduct_add, dotProduct_smul]
      have := sd_comb_pos ha hb hab (sub_pos.2 h13) (sub_pos.2 h23)
      have e : a * γ + b * γ = γ := by rw [← add_mul, hab, one_mul]
      nlinarith
  have hBc : Convex ℝ B := by
    rintro z1 ⟨h11, h12⟩ z2 ⟨h21, h22⟩ a b ha hb hab
    refine ⟨fun j => ?_, ?_⟩
    · have e1 := h11 j
      have e2 := h21 j
      simp only [Prod.fst_add, Prod.smul_fst, mulVec_add, mulVec_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have e : a * d j + b * d j = d j := by rw [← add_mul, hab, one_mul]
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨h1, h2, h3⟩ ⟨h4, h5⟩
    have := h z.1 h1 h2 h4
    linarith
  obtain ⟨f, u, hA, hB⟩ := geometric_hahn_banach_open hAc hAo hBc hdisj
  let g : Fin m → ℝ := fun i => f ((fun j => if i = j then (1 : ℝ) else 0), 0)
  have hg : ∀ p : Fin m → ℝ, f (p, 0) = g ⬝ᵥ p := by
    intro p
    let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap.comp (LinearMap.inl ℝ (Fin m → ℝ) ℝ)
    have := LinearMap.pi_apply_eq_sum_univ L p
    simp only [L, LinearMap.comp_apply, LinearMap.inl_apply, ContinuousLinearMap.coe_coe,
      smul_eq_mul] at this
    rw [this]
    simp only [dotProduct, g]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hf : ∀ p t, f (p, t) = g ⬝ᵥ p + t * f (0, 1) := by
    intro p t
    have : ((p, t) : (Fin m → ℝ) × ℝ) = (p, 0) + t • (0, 1) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul, hg]
  set μ := f (0, 1)
  have hBt : ∀ p, C *ᵥ p ≤ d → ∀ t, 0 ≤ t → u ≤ g ⬝ᵥ p + t * μ := by
    intro p hp t ht
    have := hB (p, t) ⟨hp, ht⟩
    rwa [hf] at this
  have hAt : ∀ p ∈ O, Dr p < ρ → ∀ t, t < c ⬝ᵥ p - γ → g ⬝ᵥ p + t * μ < u := by
    intro p hp hp2 t ht
    have := hA (p, t) ⟨hp, hp2, ht⟩
    rwa [hf] at this
  have hμ : 0 ≤ μ := by
    by_contra hμ; push_neg at hμ
    have := hBt q hCq ((g ⬝ᵥ q - u + 1) / (-μ)) (div_nonneg (by
      have := hBt q hCq 0 le_rfl; linarith) (by linarith))
    have hne : μ ≠ 0 := ne_of_lt hμ
    have e : (g ⬝ᵥ q - u + 1) / (-μ) * μ = -(g ⬝ᵥ q - u + 1) := by
      field_simp
    linarith
  have hμp : 0 < μ := by
    rcases hμ.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have e1 := hAt q hqO hDq (c ⬝ᵥ q - γ - 1) (by linarith)
      have e2 := hBt q hCq 0 le_rfl
      rw [← h1] at e1 e2
      linarith
  obtain ⟨η0, hη0, hη0C, hη0d⟩ := sd_lp_dual C d g u q hCq (fun p hp => by
    have := hBt p hp 0 le_rfl; linarith)
  refine ⟨μ⁻¹ • η0, fun j => ?_, fun p hp hp2 => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonneg (inv_nonneg.2 hμ) (hη0 j)
  have key : g ⬝ᵥ p + (c ⬝ᵥ p - γ) * μ - u ≤ 0 := by
    apply sd_le_of_eps (K := μ) hμ
    intro ε hε
    have := hAt p hp hp2 (c ⬝ᵥ p - γ - ε) (by linarith)
    nlinarith
  have hgp : g ⬝ᵥ p = -(η0 ⬝ᵥ (C *ᵥ p)) := by
    rw [dotProduct_mulVec, hη0C, neg_dotProduct, neg_neg]
  rw [hgp] at key
  have key2 : (c ⬝ᵥ p - γ) * μ ≤ η0 ⬝ᵥ (C *ᵥ p) - η0 ⬝ᵥ d := by linarith
  rw [smul_dotProduct, dotProduct_sub, smul_eq_mul]
  have key3 : c ⬝ᵥ p - γ ≤ (η0 ⬝ᵥ (C *ᵥ p) - η0 ⬝ᵥ d) / μ := by
    rw [le_div_iff₀ hμp]; exact key2
  have e : μ⁻¹ * (η0 ⬝ᵥ d - η0 ⬝ᵥ (C *ᵥ p)) = -((η0 ⬝ᵥ (C *ᵥ p) - η0 ⬝ᵥ d) / μ) := by
    field_simp; ring
  rw [e]; linarith


theorem sd_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- Real form of the EReal convexity axiom when values are finite. -/
theorem sd_conv_real (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ) (t u θ : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hft : φ t ≠ ⊤) (hfu : φ u ≠ ⊤) :
    φ (θ * t + (1 - θ) * u) ≠ ⊤ ∧
      (φ (θ * t + (1 - θ) * u)).toReal ≤ θ * (φ t).toReal + (1 - θ) * (φ u).toReal := by
  have h := hφ.convex t u θ ht hu h0 h1
  rw [← EReal.coe_toReal hft (hφ.ne_bot t), ← EReal.coe_toReal hfu (hφ.ne_bot u),
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
  have hne : φ (θ * t + (1 - θ) * u) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h
  refine ⟨hne, ?_⟩
  rw [← EReal.coe_toReal hne (hφ.ne_bot _)] at h
  exact EReal.coe_le_coe_iff.mp h

theorem sd_core {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β) :
    ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal) := by
  let O : Set (Fin m → ℝ) := {p | ∀ i, 0 < p i}
  have hOo : IsOpen O := by
    have : O = ⋂ i, {p : Fin m → ℝ | 0 < p i} := by ext; simp [O]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hOc : Convex ℝ O := by
    intro p hp p' hp' a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := sd_comb_pos ha hb hab (hp i) (hp' i)
    linarith
  let Dr : (Fin m → ℝ) → ℝ := fun p => ∑ i, q i * (φ (p i / q i)).toReal
  have hfinO : ∀ p ∈ O, ∀ i, φ (p i / q i) ≠ ⊤ := fun p hp i =>
    hφ.ne_top_of_pos _ (div_pos (hp i) (hq i))
  have hdiv : ∀ (p p' : Fin m → ℝ) (θ : ℝ) i,
      (θ • p + (1 - θ) • p') i / q i = θ * (p i / q i) + (1 - θ) * (p' i / q i) := by
    intro p p' θ i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [(hq i).ne']
  have hDc : ConvexOn ℝ O Dr := by
    refine ⟨hOc, fun p hp p' hp' a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [Dr, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hdiv]
    have := (sd_conv_real φ hφ _ _ a (div_pos (hp i) (hq i)).le (div_pos (hp' i) (hq i)).le ha
      (by linarith) (hfinO p hp i) (hfinO p' hp' i)).2
    have := mul_le_mul_of_nonneg_left this (hq i).le
    nlinarith
  have hqO : q ∈ O := hq
  have hDq : Dr q = 0 := by
    simp [Dr, div_self (hq _).ne', hφ.map_one]
  have hphi : ∀ p : Fin m → ℝ, (∀ i, φ (p i / q i) ≠ ⊤) → phiDiv φ p q = ((Dr p : ℝ) : EReal) := by
    intro p hp
    simp only [phiDiv, Dr]
    rw [sd_coe_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [EReal.coe_mul, EReal.coe_toReal (hp i) (hφ.ne_bot _)]
  let c : Fin m → ℝ := x ᵥ* B
  have hlin : ∀ p : Fin m → ℝ, (a + B *ᵥ p) ⬝ᵥ x = a ⬝ᵥ x + c ⬝ᵥ p := by
    intro p
    rw [add_dotProduct, dotProduct_comm (B *ᵥ p) x, dotProduct_mulVec]
  obtain ⟨η, hη, hηp⟩ := sd_stepA O hOo hOc Dr hDc q hqO ρ (by rw [hDq]; exact hρ) C d
    hqU.2.1 c (β - a ⬝ᵥ x) (fun p hp hp2 hp3 => by
      have := h p ⟨fun i => (hp i).le, hp3, by
        rw [hphi p (hfinO p hp)]; exact EReal.coe_le_coe_iff.mpr hp2.le⟩
      rw [hlin] at this; linarith)
  obtain ⟨lam, hlam, hlamp⟩ := sd_stepD O hOc Dr hDc q hqO ρ (by rw [hDq]; exact hρ)
    (c - η ᵥ* C) (η ⬝ᵥ d - (β - a ⬝ᵥ x)) (fun p hp hp2 => by
      have := hηp p hp hp2
      rw [sub_dotProduct, dotProduct_sub, dotProduct_mulVec] at *
      linarith)
  -- ℓ p := (c - η ᵥ* C) ⬝ᵥ p + (η ⬝ᵥ d - (β - a ⬝ᵥ x))
  set w := c - η ᵥ* C with hw
  set κ0 := η ⬝ᵥ d - (β - a ⬝ᵥ x) with hκ0
  have hR : ∀ p : Fin m → ℝ, (a + B *ᵥ p) ⬝ᵥ x + ρ * lam + η ⬝ᵥ (d - C *ᵥ p) =
      w ⬝ᵥ p + κ0 + β + ρ * lam := by
    intro p
    rw [hlin, hw, hκ0, sub_dotProduct, dotProduct_sub, dotProduct_mulVec]
    ring
  -- convex combination with q
  have hθO : ∀ p : Fin m → ℝ, 0 ≤ p → ∀ θ : ℝ, 0 < θ → θ ≤ 1 → θ • q + (1 - θ) • p ∈ O := by
    intro p hp θ h0 h1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hp i
    have := hq i
    nlinarith [mul_pos h0 (hq i), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) (hp i)]
  have hℓθ : ∀ p : Fin m → ℝ, ∀ θ : ℝ, w ⬝ᵥ (θ • q + (1 - θ) • p) + κ0 =
      θ * (w ⬝ᵥ q + κ0) + (1 - θ) * (w ⬝ᵥ p + κ0) := by
    intro p θ
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hDθ : ∀ p : Fin m → ℝ, 0 ≤ p → (∀ i, φ (p i / q i) ≠ ⊤) → ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      Dr (θ • q + (1 - θ) • p) ≤ (1 - θ) * Dr p := by
    intro p hp hfin θ h0 h1
    simp only [Dr, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hdiv, div_self (hq i).ne']
    have h1' : φ 1 ≠ ⊤ := by rw [hφ.map_one]; exact EReal.zero_ne_top
    have := (sd_conv_real φ hφ 1 (p i / q i) θ zero_le_one (div_nonneg (hp i) (hq i).le) h0.le h1
      h1' (hfin i)).2
    rw [hφ.map_one, EReal.toReal_zero, mul_zero, zero_add] at this
    have := mul_le_mul_of_nonneg_left this (hq i).le
    nlinarith
  refine ⟨lam, η, hlam, hη, ?_⟩
  unfold dualFunction
  refine iSup₂_le fun p hp => ?_
  have hp0 : 0 ≤ p := hp
  unfold lagrangian
  rw [hR]
  by_cases hfin : ∀ i, φ (p i / q i) ≠ ⊤
  · rw [hphi p hfin, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have key : w ⬝ᵥ p + κ0 - lam * Dr p + lam * ρ ≤ 0 := by
      apply sd_le_of_theta (Y := (w ⬝ᵥ p + κ0 - lam * Dr p + lam * ρ) - (w ⬝ᵥ q + κ0) - lam * ρ)
      intro θ h0 h1
      have e1 := hlamp _ (hθO p hp0 θ h0 h1)
      rw [hℓθ] at e1
      have e2 := mul_le_mul_of_nonneg_left (hDθ p hp0 hfin θ h0 h1) hlam
      nlinarith
    linarith
  · push_neg at hfin
    obtain ⟨i0, hi0⟩ := hfin
    have htop : phiDiv φ p q = ⊤ := by
      unfold phiDiv
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hi0,
        EReal.coe_mul_top_of_pos (hq i0)]
      apply EReal.top_add_of_ne_bot
      refine Finset.sum_induction _ (fun z : EReal => z ≠ ⊥) ?_ ?_ ?_
      · intro a b ha hb
        exact EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩
      · exact EReal.zero_ne_bot
      · intro i _
        rw [EReal.mul_ne_bot]
        have hqi : (0 : EReal) < (q i : EReal) := EReal.coe_pos.mpr (hq i)
        exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hφ.ne_bot _), Or.inl (EReal.coe_ne_top _),
          Or.inl hqi.le⟩
    rw [htop]
    rcases hlam.lt_or_eq with hl | hl
    · rw [EReal.coe_mul_top_of_pos hl, EReal.sub_top]
      exact bot_le
    · rw [← hl, EReal.coe_zero, zero_mul, sub_zero, EReal.coe_le_coe_iff]
      have key : w ⬝ᵥ p + κ0 ≤ 0 := by
        apply sd_le_of_theta (Y := (w ⬝ᵥ p + κ0) - (w ⬝ᵥ q + κ0))
        intro θ h0 h1
        have e1 := hlamp _ (hθO p hp0 θ h0 h1)
        rw [hℓθ, ← hl, zero_mul] at e1
        nlinarith
      linarith

end PhiDivRobust.Counterpart

open PhiDivRobust.Counterpart


theorem solution {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β) :
    ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal) := by
  exact sd_core φ hφ a B β C d q ρ hq hρ hqU x h
