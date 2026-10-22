-- Prove2me | solution 1 for SelfDualLP.Complexity.theorem_3_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:14:23.733989+00:00
-- url     : https://prove2.me/submissions/26165cdb-2b7d-4e35-90e8-db9a58fc6945

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence
import Definitions.Def_SelfDualLP_Complexity_Termination
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix


namespace SelfDualLP.Complexity


section LPBsec
namespace LPB

open Matrix

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

end LPB
end LPBsec

section Hlp

abbrev RowI (m n : ℕ) := Fin m ⊕ Fin n ⊕ Unit ⊕ Unit
abbrev ColI (m n : ℕ) := Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit ⊕ Fin n ⊕ Unit

variable {m n : ℕ}

/-- columns of the constraint matrix -/
noncomputable def hCol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ) :
    ColI m n → (RowI m n → ℝ) :=
  Sum.elim
    (fun i => Sum.elim (fun _ => 0) (Sum.elim (fun j => A i j) (Sum.elim (fun _ => -b i) (fun _ => 0))))
    (Sum.elim
      (fun i => Sum.elim (fun _ => 0) (Sum.elim (fun j => -A i j) (Sum.elim (fun _ => b i) (fun _ => 0))))
      (Sum.elim
        (fun j => Sum.elim (fun i => A i j) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => c j) (fun _ => s0 j))))
        (Sum.elim
          (fun _ => Sum.elim (fun i => -b i) (Sum.elim (fun j => -c j) (Sum.elim (fun _ => 0) (fun _ => 1))))
          (Sum.elim
            (fun j => Sum.elim (fun _ => 0) (Sum.elim (fun j' => if j' = j then 1 else 0) (Sum.elim (fun _ => 0) (fun _ => x0 j))))
            (fun _ => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 1))))))))

noncomputable def hM (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ) :
    Matrix (RowI m n) (ColI m n) ℝ :=
  Matrix.of fun r k => hCol A b c x0 s0 k r

lemma hlp_exists_aux (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) (x0 ⬝ᵥ s0 + 1) ∈ LPB.cone (hM A b c x0 s0) := by
  by_contra hnot
  obtain ⟨yv, hy, hyt⟩ := LPB.farkas _ _ hnot
  set p : Fin m → ℝ := fun i => yv (Sum.inl i) with hp
  set q : Fin n → ℝ := fun j => yv (Sum.inr (Sum.inl j)) with hq
  set r : ℝ := yv (Sum.inr (Sum.inr (Sum.inl ()))) with hr
  set ρ : ℝ := yv (Sum.inr (Sum.inr (Sum.inr ()))) with hρ
  have hpos : 0 < x0 ⬝ᵥ s0 + 1 := by
    have : 0 ≤ x0 ⬝ᵥ s0 := Finset.sum_nonneg (fun j _ => (mul_pos (hx0 j) (hs0 j)).le)
    linarith
  have hρneg : ρ < 0 := by
    have : yv ⬝ᵥ Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) (x0 ⬝ᵥ s0 + 1) = ρ * (x0 ⬝ᵥ s0 + 1) := by
      simp [dotProduct_single, hρ]
    rw [this] at hyt
    by_contra h; push_neg at h
    nlinarith
  have col : ∀ k, (yv ᵥ* hM A b c x0 s0) k = yv ⬝ᵥ hCol A b c x0 s0 k := by
    intro k; simp [vecMul, dotProduct, hM]
  have hyp : ∀ i, 0 ≤ ∑ j, q j * A i j - r * b i := by
    intro i
    have := hy (Sum.inl i)
    rw [col] at this
    simpa [dotProduct, hCol, Fintype.sum_sum_type, hq, hr, mul_comm] using this
  have hym : ∀ i, 0 ≤ -(∑ j, q j * A i j) + r * b i := by
    intro i
    have := hy (Sum.inr (Sum.inl i))
    rw [col] at this
    simpa [dotProduct, hCol, Fintype.sum_sum_type, hq, hr, mul_comm, Finset.sum_neg_distrib] using this
  have hx : ∀ j, 0 ≤ ∑ i, p i * A i j + r * c j + ρ * s0 j := by
    intro j
    have := hy (Sum.inr (Sum.inr (Sum.inl j)))
    rw [col] at this
    simp [dotProduct, hCol, Fintype.sum_sum_type, hp, hr, hρ, mul_comm] at this ⊢
    linarith
  have hτ : 0 ≤ -(∑ i, p i * b i) - ∑ j, q j * c j + ρ := by
    have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
    rw [col] at this
    simp [dotProduct, hCol, Fintype.sum_sum_type, hp, hq, hρ, mul_comm, Finset.sum_neg_distrib, sub_eq_add_neg] at this ⊢
    linarith
  have hs : ∀ j, 0 ≤ q j + ρ * x0 j := by
    intro j
    have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
    rw [col] at this
    simpa [dotProduct, hCol, Fintype.sum_sum_type, hq, hρ, mul_comm] using this
  have hκ : 0 ≤ r + ρ := by
    have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
    rw [col] at this
    simpa [dotProduct, hCol, Fintype.sum_sum_type, hr, hρ, mul_comm] using this
  have hAq : ∀ i, ∑ j, q j * A i j = r * b i := fun i => le_antisymm (by linarith [hym i]) (by linarith [hyp i])
  have hq0 : ∀ j, 0 ≤ q j := fun j => by nlinarith [hs j, hx0 j]
  have e1 : ∑ i, p i * (∑ j, q j * A i j) = ∑ j, q j * (∑ i, p i * A i j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  have e2 : ∑ i, p i * (∑ j, q j * A i j) = r * ∑ i, p i * b i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hAq i]; ring)
  have e3 : ∑ j, q j * (∑ i, p i * A i j) ≥ ∑ j, q j * (-(r * c j) - ρ * s0 j) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (by linarith [hx j]) (hq0 j))
  have e4 : ∑ j, q j * (-(r * c j) - ρ * s0 j) = -r * ∑ j, q j * c j - ρ * ∑ j, q j * s0 j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hQ : 0 ≤ ∑ j, q j * s0 j := Finset.sum_nonneg (fun j _ => mul_nonneg (hq0 j) (hs0 j).le)
  have hrpos : 0 < r := by linarith
  have key : r * (∑ i, p i * b i + ∑ j, q j * c j) ≥ -ρ * ∑ j, q j * s0 j := by
    nlinarith
  have h2 : r * (∑ i, p i * b i + ∑ j, q j * c j) ≤ r * ρ := by
    apply mul_le_mul_of_nonneg_left _ hrpos.le
    linarith
  nlinarith


lemma dot_mulVec_transpose (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin n → ℝ) (v : Fin m → ℝ) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

lemma hlp_eq4 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 x s : Fin n → ℝ)
    (y0 y : Fin m → ℝ) (τ κ : ℝ)
    (E1 : A *ᵥ x = τ • b) (E2 : s = -(Aᵀ *ᵥ y) + τ • c) (E3 : κ = b ⬝ᵥ y - c ⬝ᵥ x) :
    -(bbar A b x0 ⬝ᵥ y) + cbar A c y0 s0 ⬝ᵥ x - zbar b c x0 y0 * τ
      = -(x0 ⬝ᵥ s) - (s0 ⬝ᵥ x) - τ - κ := by
  have h1 : (A *ᵥ x0) ⬝ᵥ y = x0 ⬝ᵥ (Aᵀ *ᵥ y) := dot_mulVec_transpose A x0 y
  have h2 : (Aᵀ *ᵥ y0) ⬝ᵥ x = y0 ⬝ᵥ (A *ᵥ x) := by
    rw [dotProduct_comm, ← dot_mulVec_transpose]; rw [dotProduct_comm]
  have h3 : x0 ⬝ᵥ (Aᵀ *ᵥ y) = τ * (x0 ⬝ᵥ c) - x0 ⬝ᵥ s := by
    have : Aᵀ *ᵥ y = τ • c - s := by rw [E2]; abel
    rw [this, dotProduct_sub, dotProduct_smul]; simp
  have h4 : y0 ⬝ᵥ (A *ᵥ x) = τ * (y0 ⬝ᵥ b) := by rw [E1, dotProduct_smul]; simp
  unfold bbar cbar zbar
  rw [sub_dotProduct, sub_dotProduct, sub_dotProduct, h1, h2, h3, h4, E3]
  rw [dotProduct_comm c x0, dotProduct_comm y0 b]
  ring

lemma hlp_obj (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ) (y0 : Fin m → ℝ)
    (w : HLPPoint m n) (hw : HLPFeasible A b c x0 y0 s0 w) :
    hlpObjective x0 s0 w = w.x ⬝ᵥ w.s + w.τ * w.κ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hw
  have e1 : A *ᵥ w.x = w.τ • b - w.θ • bbar A b x0 := by
    rw [sub_eq_add_neg, ← sub_eq_zero]; rw [← h1]; abel_nf
  have h5 : (A *ᵥ w.x) ⬝ᵥ w.y = w.x ⬝ᵥ (Aᵀ *ᵥ w.y) := dot_mulVec_transpose A w.x w.y
  rw [e1, sub_dotProduct, smul_dotProduct, smul_dotProduct] at h5
  have h6 : w.x ⬝ᵥ w.s = -(w.x ⬝ᵥ (Aᵀ *ᵥ w.y)) + w.τ * (w.x ⬝ᵥ c) - w.θ * (w.x ⬝ᵥ cbar A c y0 s0) := by
    rw [h2, dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul, dotProduct_smul]; simp
  rw [dotProduct_comm (bbar A b x0) w.y, dotProduct_comm (cbar A c y0 s0) w.x] at *
  rw [dotProduct_comm w.x c] at h6
  unfold hlpObjective
  have h7 : w.τ * w.κ = w.τ * (b ⬝ᵥ w.y) - w.τ * (c ⬝ᵥ w.x) + w.τ * zbar b c x0 y0 * w.θ := by
    rw [h3]; ring
  rw [h6, h7]
  simp only [smul_eq_mul] at h5
  linear_combination w.θ * h4 - h5

lemma hlp_exists (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ)
    (y0 : Fin m → ℝ) (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    ∃ w : HLPPoint m n, HLPFeasible A b c x0 y0 s0 w ∧ w.θ = 0 := by
  obtain ⟨z, hz, hMz⟩ := hlp_exists_aux A b c x0 s0 hx0 hs0
  have hrow : ∀ r, ∑ k, hCol A b c x0 s0 k r * z k =
      (Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) (x0 ⬝ᵥ s0 + 1) : RowI m n → ℝ) r := by
    intro r
    have := congrFun hMz r
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hM] using this
  set X : Fin n → ℝ := fun j => z (Sum.inr (Sum.inr (Sum.inl j))) with hX
  set Y : Fin m → ℝ := fun i => z (Sum.inl i) - z (Sum.inr (Sum.inl i)) with hY
  set T : ℝ := z (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) with hT
  set S : Fin n → ℝ := fun j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) with hS
  set K : ℝ := z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))) with hK
  have E1 : A *ᵥ X = T • b := by
    funext i
    have := hrow (Sum.inl i)
    simp [hCol, Fintype.sum_sum_type] at this
    simp [Matrix.mulVec, dotProduct, hX, hT, mul_comm]
    linarith
  have E2 : S = -(Aᵀ *ᵥ Y) + T • c := by
    funext j
    have := hrow (Sum.inr (Sum.inl j))
    simp [hCol, Fintype.sum_sum_type] at this
    simp [Matrix.mulVec, dotProduct, hY, hT, hS, mul_comm, mul_sub, Finset.sum_sub_distrib]
    linarith
  have E3 : K = b ⬝ᵥ Y - c ⬝ᵥ X := by
    have := hrow (Sum.inr (Sum.inr (Sum.inl ())))
    simp [hCol, Fintype.sum_sum_type] at this
    simp [dotProduct, hY, hX, hK, mul_sub, Finset.sum_sub_distrib]
    linarith
  have E4 : s0 ⬝ᵥ X + x0 ⬝ᵥ S + T + K = x0 ⬝ᵥ s0 + 1 := by
    have := hrow (Sum.inr (Sum.inr (Sum.inr ())))
    simp [hCol, Fintype.sum_sum_type] at this
    simp [dotProduct, hX, hS, hT, hK] at this ⊢
    linarith
  refine ⟨⟨Y, X, T, 0, S, K⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · simp [E1]
  · simp [E2]
  · simp [E3]
  · have := hlp_eq4 A b c x0 s0 X S y0 Y T K E1 E2 E3
    dsimp only
    linarith
  · exact fun j => hz _
  · exact hz _
  · exact fun j => hz _
  · exact hz _

end Hlp

section Main

variable {m n : ℕ}

lemma ones_dot_ones : ones n ⬝ᵥ ones n = (n : ℝ) := by simp [ones, dotProduct]

lemma ones_pos (j : Fin n) : 0 < ones n j := by simp [ones]

lemma ones_dot (v : Fin n → ℝ) : ones n ⬝ᵥ v = ∑ j, v j := by simp [ones, dotProduct]

lemma dot_ones (v : Fin n → ℝ) : v ⬝ᵥ ones n = ∑ j, v j := by simp [ones, dotProduct]

lemma dot_nonneg {u v : Fin n → ℝ} (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) : 0 ≤ u ⬝ᵥ v :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hu j) (hv j))

/-- The linear (homogeneous) part of the HLP equations under (7). -/
def Eqs (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (z : HLPPoint m n) : Prop :=
  A *ᵥ z.x - z.τ • b + z.θ • bbar A b (ones n) = 0 ∧
  z.s = -(Aᵀ *ᵥ z.y) + z.τ • c - z.θ • cbar A c 0 (ones n) ∧
  z.κ = b ⬝ᵥ z.y - c ⬝ᵥ z.x + zbar b c (ones n) 0 * z.θ

/-- The residual of row (4). -/
def Lres (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (z : HLPPoint m n) : ℝ :=
  -(bbar A b (ones n) ⬝ᵥ z.y) + cbar A c 0 (ones n) ⬝ᵥ z.x - zbar b c (ones n) 0 * z.τ

lemma cross_gen (A : Matrix (Fin m) (Fin n) ℝ) (b bb : Fin m → ℝ) (c cb : Fin n → ℝ) (zb : ℝ)
    (z z' : HLPPoint m n)
    (h1 : A *ᵥ z.x - z.τ • b + z.θ • bb = 0) (h2 : z.s = -(Aᵀ *ᵥ z.y) + z.τ • c - z.θ • cb)
    (h3 : z.κ = b ⬝ᵥ z.y - c ⬝ᵥ z.x + zb * z.θ)
    (h1' : A *ᵥ z'.x - z'.τ • b + z'.θ • bb = 0)
    (h2' : z'.s = -(Aᵀ *ᵥ z'.y) + z'.τ • c - z'.θ • cb)
    (h3' : z'.κ = b ⬝ᵥ z'.y - c ⬝ᵥ z'.x + zb * z'.θ) :
    z.x ⬝ᵥ z'.s + z.τ * z'.κ + (z'.x ⬝ᵥ z.s + z'.τ * z.κ) =
      -(z.θ * (-(bb ⬝ᵥ z'.y) + cb ⬝ᵥ z'.x - zb * z'.τ)) -
        z'.θ * (-(bb ⬝ᵥ z.y) + cb ⬝ᵥ z.x - zb * z.τ) := by
  have key : ∀ (u v : HLPPoint m n), A *ᵥ u.x - u.τ • b + u.θ • bb = 0 →
      v.s = -(Aᵀ *ᵥ v.y) + v.τ • c - v.θ • cb →
      u.x ⬝ᵥ v.s = -(u.τ * (b ⬝ᵥ v.y)) + u.θ * (bb ⬝ᵥ v.y) + v.τ * (c ⬝ᵥ u.x)
        - v.θ * (cb ⬝ᵥ u.x) := by
    intro u v hu hv
    have e1 : A *ᵥ u.x = u.τ • b - u.θ • bb := eq_of_sub_eq_zero (by rw [← hu]; abel)
    have h5 : (A *ᵥ u.x) ⬝ᵥ v.y = u.x ⬝ᵥ (Aᵀ *ᵥ v.y) := dot_mulVec_transpose A u.x v.y
    rw [e1, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h5
    rw [hv, dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, dotProduct_comm u.x c, dotProduct_comm u.x cb]
    linarith
  rw [key z z' h1 h2', key z' z h1' h2]
  simp only [h3, h3']
  ring

lemma cross (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (z z' : HLPPoint m n)
    (hz : Eqs A b c z) (hz' : Eqs A b c z') :
    z.x ⬝ᵥ z'.s + z.τ * z'.κ + (z'.x ⬝ᵥ z.s + z'.τ * z.κ) =
      -(z.θ * Lres A b c z') - z'.θ * Lres A b c z :=
  cross_gen A b _ c _ _ z z' hz.1 hz.2.1 hz.2.2 hz'.1 hz'.2.1 hz'.2.2

lemma gap_eqs (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (z : HLPPoint m n)
    (hz : Eqs A b c z) : gap z = -(z.θ * Lres A b c z) := by
  have := cross A b c z z hz hz
  unfold gap; linarith

lemma feas7_eqs {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    (hz : HLPFeasible7 A b c z) : Eqs A b c z ∧ Lres A b c z = -(n : ℝ) - 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hz
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  unfold Lres; rw [h4, ones_dot_ones]

lemma inQ7_eqs {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {d : HLPPoint m n}
    (hd : InQ7 A b c d) : Eqs A b c d ∧ Lres A b c d = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hd
  refine ⟨⟨h1, (sub_eq_zero.mp h2).symm, (sub_eq_zero.mp h3).symm⟩, h4⟩

lemma gap_feas7 {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    (hz : HLPFeasible7 A b c z) : gap z = ((n : ℝ) + 1) * z.θ := by
  obtain ⟨he, hL⟩ := feas7_eqs hz
  rw [gap_eqs A b c z he, hL]; ring

lemma mu_feas7 {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    (hz : HLPFeasible7 A b c z) : mu z = z.θ := by
  unfold mu; rw [gap_feas7 hz]; field_simp

lemma gap_dir {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {d : HLPPoint m n}
    (hd : InQ7 A b c d) : gap d = 0 := by
  obtain ⟨he, hL⟩ := inQ7_eqs hd
  rw [gap_eqs A b c d he, hL]; ring

lemma eqs_move {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    (hz : Eqs A b c z) (hd : Eqs A b c d) (α : ℝ) : Eqs A b c (z.move d α) := by
  obtain ⟨z1, z2, z3⟩ := hz
  obtain ⟨d1, d2, d3⟩ := hd
  refine ⟨?_, ?_, ?_⟩
  · funext i
    have e1 := congrFun z1 i
    have e2 := congrFun d1 i
    simp only [HLPPoint.move, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, mulVec_add, mulVec_smul] at e1 e2 ⊢
    linear_combination e1 + α * e2
  · funext j
    have e1 := congrFun z2 j
    have e2 := congrFun d2 j
    simp only [HLPPoint.move, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.neg_apply, mulVec_add, mulVec_smul] at e1 e2 ⊢
    linear_combination e1 + α * e2
  · simp only [HLPPoint.move, dotProduct_add, dotProduct_smul, smul_eq_mul]
    linear_combination z3 + α * d3

lemma Lres_move (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (z d : HLPPoint m n)
    (α : ℝ) : Lres A b c (z.move d α) = Lres A b c z + α * Lres A b c d := by
  simp only [Lres, HLPPoint.move, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

lemma move_zero (z d : HLPPoint m n) : z.move d 0 = z := by
  cases z; simp [HLPPoint.move]

lemma gap_move (z d : HLPPoint m n) (α : ℝ) :
    gap (z.move d α) = gap z + α * (∑ j, (z.x j * d.s j + z.s j * d.x j) +
      (z.τ * d.κ + z.κ * d.τ)) + α ^ 2 * gap d := by
  simp only [gap, HLPPoint.move, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ j, (z.x j + α * d.x j) * (z.s j + α * d.s j) = z.x j * z.s j +
      α * (z.x j * d.s j + z.s j * d.x j) + α ^ 2 * (d.x j * d.s j) := fun j => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma pc_sum {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    {γ : ℝ} (hd : IsPCDirection A b c z d γ) :
    ∑ j, (z.x j * d.s j + z.s j * d.x j) + (z.τ * d.κ + z.κ * d.τ) = (γ - 1) * gap z := by
  have h1 : ∀ j, z.x j * d.s j + z.s j * d.x j = γ * mu z - z.x j * z.s j := hd.2.1
  rw [Finset.sum_congr rfl (fun j _ => h1 j), hd.2.2, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmu : mu z * ((n : ℝ) + 1) = gap z := by
    unfold mu; field_simp
  unfold gap at hmu ⊢
  simp only [dotProduct] at hmu ⊢
  linear_combination γ * hmu

lemma gap_move_pc {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    {γ : ℝ} (hd : IsPCDirection A b c z d γ) (α : ℝ) :
    gap (z.move d α) = (1 + α * (γ - 1)) * gap z := by
  rw [gap_move, pc_sum hd, gap_dir hd.1]; ring

lemma gap_pos_of_pos {z : HLPPoint m n} (hx : ∀ j, 0 < z.x j) (hτ : 0 < z.τ) (hs : ∀ j, 0 < z.s j)
    (hκ : 0 < z.κ) : 0 < gap z := by
  unfold gap
  have := dot_nonneg (fun j => (hx j).le) (fun j => (hs j).le)
  have := mul_pos hτ hκ
  linarith

/-! ### Initial point -/

lemma initial_feas (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    HLPStrictlyFeasible7 A b c (initialPoint m n) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [initialPoint, bbar, cbar, zbar, ones_dot_ones, ones]
  ring

end Main

section LPpart

variable {m n : ℕ}

theorem t2iv_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (∃ z : HLPPoint m n, HLPOptimal A b c x0 y0 s0 z ∧ hlpObjective x0 s0 z = 0) ∧
    ∀ z : HLPPoint m n, HLPFeasible A b c x0 y0 s0 z →
      (x0 ⬝ᵥ s0 + 1) * z.θ = z.x ⬝ᵥ z.s + z.τ * z.κ := by
  refine ⟨?_, fun w hw => hlp_obj A b c x0 s0 y0 w hw⟩
  obtain ⟨w, hw, hθ⟩ := hlp_exists A b c x0 s0 y0 hx0 hs0
  have h0 : hlpObjective x0 s0 w = 0 := by simp [hlpObjective, hθ]
  refine ⟨w, ⟨hw, fun v hv => ?_⟩, h0⟩
  rw [h0, hlp_obj A b c x0 s0 y0 v hv]
  obtain ⟨-, -, -, -, hx, hτ, hs, hκ⟩ := hv
  have : 0 ≤ v.x ⬝ᵥ v.s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))
  have := mul_nonneg hτ hκ
  linarith

lemma lpFeas_iff {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {x : Fin n → ℝ} :
    x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c) ↔
      A *ᵥ x = b ∧ ∀ j, 0 ≤ x j := by
  rw [LinearOptimization.generalFeasibleSet_stdFormLP]
  simp only [LinearOptimization.stdPolyhedron, Set.mem_setOf_eq, Pi.le_def, Pi.zero_apply]

lemma dualFeas_iff {A : Matrix (Fin m) (Fin n) ℝ} {c : Fin n → ℝ} {y : Fin m → ℝ} :
    y ∈ LinearOptimization.dualFeasibleStd A c ↔ ∀ j, (Aᵀ *ᵥ y) j ≤ c j := by
  simp only [LinearOptimization.dualFeasibleStd, Set.mem_setOf_eq, Pi.le_def]

lemma weak_dual {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : A *ᵥ x = b) (hx0 : ∀ j, 0 ≤ x j) (hy : ∀ j, (Aᵀ *ᵥ y) j ≤ c j) :
    b ⬝ᵥ y ≤ c ⬝ᵥ x := by
  rw [← hx, dot_mulVec_transpose, dotProduct_comm c]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (hx0 j))

lemma farkas2 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ)
    (h : ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → A *ᵥ x = b → β < c ⬝ᵥ x) :
    ∃ p : Fin m → ℝ, ∃ q : ℝ, 0 ≤ q ∧ (∀ j, 0 ≤ (p ᵥ* A) j + q * c j) ∧
      p ⬝ᵥ b + q * β < 0 := by
  let M : Matrix (Fin m ⊕ Unit) (Fin n ⊕ Unit) ℝ := Matrix.of fun r k =>
    Sum.elim (fun i => Sum.elim (fun j => A i j) (fun _ => (0 : ℝ)) k)
      (fun _ => Sum.elim (fun j => c j) (fun _ => (1 : ℝ)) k) r
  let t : Fin m ⊕ Unit → ℝ := Sum.elim b (fun _ => β)
  have hnot : t ∉ LPB.cone M := by
    rintro ⟨z, hz, hMz⟩
    have hrow : ∀ r, (M *ᵥ z) r = t r := fun r => by
      have := congrFun hMz r
      simpa [Matrix.mulVecLin_apply] using this
    let x : Fin n → ℝ := fun j => z (Sum.inl j)
    have hAx : A *ᵥ x = b := by
      funext i
      have := hrow (Sum.inl i)
      simpa [M, t, x, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this
    have hcx : c ⬝ᵥ x + z (Sum.inr ()) = β := by
      have := hrow (Sum.inr ())
      simpa [M, t, x, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm] using this
    have := h x (fun j => hz _) hAx
    have := hz (Sum.inr ())
    linarith
  obtain ⟨yv, hy, hyt⟩ := LPB.farkas M t hnot
  refine ⟨fun i => yv (Sum.inl i), yv (Sum.inr ()), ?_, fun j => ?_, ?_⟩
  · have := hy (Sum.inr ())
    simpa [M, vecMul, dotProduct, Fintype.sum_sum_type] using this
  · have := hy (Sum.inl j)
    simpa [M, vecMul, dotProduct, Fintype.sum_sum_type] using this
  · simpa [t, dotProduct, Fintype.sum_sum_type, mul_comm] using hyt

lemma dual_near {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {xb : Fin n → ℝ} (hxo : SelfDualLP.Complexity.LPOptimal A b c xb) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin m → ℝ, (∀ j, (Aᵀ *ᵥ y) j ≤ c j) ∧ c ⬝ᵥ xb - ε < b ⬝ᵥ y := by
  obtain ⟨hxf, hxmin⟩ := hxo
  obtain ⟨hAx, hx0⟩ := lpFeas_iff.mp hxf
  obtain ⟨p, q, hq, hpq, hpb⟩ := farkas2 A b c (c ⬝ᵥ xb - ε) (fun x hx0' hAx' => by
    have := hxmin x (lpFeas_iff.mpr ⟨hAx', hx0'⟩)
    linarith)
  have hpb' : -(q * (c ⬝ᵥ xb)) ≤ p ⬝ᵥ b := by
    rw [← hAx, Matrix.dotProduct_mulVec]
    have : ∑ j, (-(q * c j)) * xb j ≤ ∑ j, (p ᵥ* A) j * xb j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (by linarith [hpq j]) (hx0 j))
    have e : ∑ j, (-(q * c j)) * xb j = -(q * (c ⬝ᵥ xb)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e] at this
    simp only [dotProduct] at this ⊢
    linarith
  have hqpos : 0 < q := by
    by_contra hq0
    have : q = 0 := le_antisymm (not_lt.mp hq0) hq
    subst this
    simp at hpb hpb'
    linarith
  refine ⟨(-q⁻¹) • p, fun j => ?_, ?_⟩
  · have e : (Aᵀ *ᵥ ((-q⁻¹) • p)) j = -((p ᵥ* A) j) / q := by
      rw [mulVec_smul, mulVec_transpose]; simp [div_eq_mul_inv]; ring
    rw [e, div_le_iff₀ hqpos]
    linarith [hpq j]
  · have e : b ⬝ᵥ ((-q⁻¹) • p) = -(p ⬝ᵥ b) / q := by
      rw [dotProduct_smul, dotProduct_comm]; simp [div_eq_mul_inv]; ring
    rw [e, lt_div_iff₀ hqpos]
    linarith

lemma strong_dual {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {xb : Fin n → ℝ} {yb : Fin m → ℝ} {sb : Fin n → ℝ}
    (hx : SelfDualLP.Complexity.LPOptimal A b c xb)
    (hy : SelfDualLP.Complexity.LDOptimal A b c yb sb) : b ⬝ᵥ yb = c ⬝ᵥ xb := by
  obtain ⟨⟨hyf, hymax⟩, -⟩ := hy
  obtain ⟨hAx, hx0⟩ := lpFeas_iff.mp hx.1
  have h1 := weak_dual hAx hx0 (dualFeas_iff.mp hyf)
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨y, hyd, hyb⟩ := dual_near hx (c ⬝ᵥ xb - b ⬝ᵥ yb) (by linarith)
  have := hymax y (dualFeas_iff.mpr hyd)
  rw [dotProduct_comm y, dotProduct_comm yb] at this
  linarith

lemma ld_feas_of_opt {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    (h : SelfDualLP.Complexity.LPHasSolution A b c) : SelfDualLP.Complexity.LDIsFeasible A c := by
  obtain ⟨xb, hxb⟩ := h
  obtain ⟨y, hy, -⟩ := dual_near hxb 1 one_pos
  exact ⟨y, dualFeas_iff.mpr hy⟩

lemma recession {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    (hf : ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b)
    (hno : ¬ SelfDualLP.Complexity.LPHasSolution A b c) :
    ∃ d : Fin n → ℝ, (∀ j, 0 ≤ d j) ∧ A *ᵥ d = 0 ∧ c ⬝ᵥ d < 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, q, hq, hpq, hpb⟩ := farkas2 A 0 c (-1) (fun d hd hAd => by
    have := hcon d hd hAd; linarith)
  have hqpos : 0 < q := by simp at hpb; linarith
  have hyd : ∀ j, (Aᵀ *ᵥ ((-q⁻¹) • p)) j ≤ c j := by
    intro j
    have e : (Aᵀ *ᵥ ((-q⁻¹) • p)) j = -((p ᵥ* A) j) / q := by
      rw [mulVec_smul, mulVec_transpose]; simp [div_eq_mul_inv]; ring
    rw [e, div_le_iff₀ hqpos]
    linarith [hpq j]
  obtain ⟨x0, hx00, hAx0⟩ := hf
  obtain ⟨zs, hzs, -, hmin⟩ := LPB.attain A b c (b ⬝ᵥ ((-q⁻¹) • p))
    (fun z hz => weak_dual hz.2 hz.1 hyd) x0 ⟨hx00, hAx0⟩
  apply hno
  refine ⟨zs, lpFeas_iff.mpr ⟨hzs.2, hzs.1⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := lpFeas_iff.mp hx
  exact hmin x ⟨h2, h1⟩

lemma ray_point (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hno : ¬ SelfDualLP.Complexity.LPHasSolution A b c) :
    ∃ w : HLPPoint m n, Eqs A b c w ∧ w.θ = 0 ∧ w.τ = 0 ∧ 0 < w.κ ∧
      (∀ j, 0 ≤ w.x j) ∧ (∀ j, 0 ≤ w.s j) := by
  by_cases hf : ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b
  · obtain ⟨d, hd0, hAd, hcd⟩ := recession hf hno
    refine ⟨⟨0, d, 0, 0, 0, -(c ⬝ᵥ d)⟩, ⟨?_, ?_, ?_⟩, rfl, rfl, by simp; linarith, hd0,
      fun j => le_rfl⟩
    · simp [hAd]
    · simp
    · simp
  · obtain ⟨p, hp, hpb⟩ := LPB.farkas A b (by
      rintro ⟨z, hz, hAz⟩
      exact hf ⟨z, hz, by simpa [Matrix.mulVecLin_apply] using hAz⟩)
    refine ⟨⟨-p, 0, 0, 0, Aᵀ *ᵥ p, -(b ⬝ᵥ p)⟩, ⟨?_, ?_, ?_⟩, rfl, rfl, ?_, fun j => le_rfl,
      fun j => ?_⟩
    · simp
    · simp [mulVec_neg]
    · simp
    · rw [dotProduct_comm]; simp; linarith
    · rw [mulVec_transpose]; exact hp j

theorem t3ii_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) (hτ : z.τ = 0) :
    0 < z.κ ∧ c ⬝ᵥ z.x - b ⬝ᵥ z.y < 0 ∧ (c ⬝ᵥ z.x < 0 ∨ -(b ⬝ᵥ z.y) < 0) ∧
    (c ⬝ᵥ z.x < 0 → ¬ SelfDualLP.Complexity.LDIsFeasible A c) ∧
    (-(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c) ∧
    (c ⬝ᵥ z.x < 0 ∧ -(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c ∧
      ¬ SelfDualLP.Complexity.LDIsFeasible A c) := by
  obtain ⟨⟨hf, -⟩, hθ, -, hτκ⟩ := hz
  obtain ⟨e1, e2, e3, -, hx, -, hs, -⟩ := hf
  simp only [hτ, hθ, zero_smul, sub_zero, add_zero, zero_mul, mul_zero] at e1 e2 e3
  have hκ : 0 < z.κ := by linarith
  have hLD : c ⬝ᵥ z.x < 0 → ¬ SelfDualLP.Complexity.LDIsFeasible A c := by
    rintro hc ⟨y', hy'⟩
    have hy'' := dualFeas_iff.mp hy'
    have h0 : (A *ᵥ z.x) ⬝ᵥ y' = 0 := by rw [e1]; simp
    rw [dot_mulVec_transpose] at h0
    have h2 : z.x ⬝ᵥ (Aᵀ *ᵥ y') ≤ z.x ⬝ᵥ c :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy'' j) (hx j))
    rw [dotProduct_comm c] at hc
    linarith
  have hLP : -(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c := by
    rintro hb ⟨x', hx'⟩
    obtain ⟨hAx', hx0'⟩ := lpFeas_iff.mp hx'
    have h1 : b ⬝ᵥ z.y = x' ⬝ᵥ (Aᵀ *ᵥ z.y) := by rw [← hAx', dot_mulVec_transpose]
    have h2 : Aᵀ *ᵥ z.y = -z.s := by rw [e2]; simp
    rw [h2, dotProduct_neg] at h1
    have := dot_nonneg hx0' hs
    linarith
  refine ⟨hκ, by linarith, ?_, hLD, hLP, fun h => ⟨hLP h.2, hLD h.1⟩⟩
  by_contra hcon
  push_neg at hcon
  linarith [hcon.1, hcon.2]

theorem t3i_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) :
    (SelfDualLP.Complexity.LPHasSolution A b c ↔ 0 < z.τ) ∧
    (0 < z.τ → SelfDualLP.Complexity.LPOptimal A b c (z.τ⁻¹ • z.x) ∧
      SelfDualLP.Complexity.LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s)) := by
  have hz' := hz
  obtain ⟨⟨hf, -⟩, hθ, -, -⟩ := hz
  obtain ⟨e1, e2, e3, -, hx, hτ0, hs, hκ0⟩ := hf
  rw [hθ] at e1 e2 e3
  simp only [zero_smul, sub_zero, add_zero, mul_zero] at e1 e2 e3
  have key : 0 < z.τ → SelfDualLP.Complexity.LPOptimal A b c (z.τ⁻¹ • z.x) ∧
      SelfDualLP.Complexity.LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s) := by
    intro hτ
    have hAx : A *ᵥ (z.τ⁻¹ • z.x) = b := by
      have : A *ᵥ z.x = z.τ • b := by rw [← sub_eq_zero]; exact e1
      rw [mulVec_smul, this, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    have hx0 : ∀ j, 0 ≤ (z.τ⁻¹ • z.x) j := fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hτ.le) (hx j)
    have hsd : z.τ⁻¹ • z.s = c - Aᵀ *ᵥ (z.τ⁻¹ • z.y) := by
      rw [e2, mulVec_smul]
      funext j
      simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hyd : ∀ j, (Aᵀ *ᵥ (z.τ⁻¹ • z.y)) j ≤ c j := fun j => by
      have h1 := congrFun hsd j
      have h2 : 0 ≤ (z.τ⁻¹ • z.s) j := by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hτ.le) (hs j)
      simp only [Pi.sub_apply] at h1
      linarith
    have hgap : c ⬝ᵥ (z.τ⁻¹ • z.x) ≤ b ⬝ᵥ (z.τ⁻¹ • z.y) := by
      rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hτ.le)
    refine ⟨⟨lpFeas_iff.mpr ⟨hAx, hx0⟩, fun x' hx' => ?_⟩, ⟨⟨dualFeas_iff.mpr hyd, fun q hq => ?_⟩, hsd⟩⟩
    · obtain ⟨h1, h2⟩ := lpFeas_iff.mp hx'
      have := weak_dual h1 h2 hyd
      linarith
    · have := weak_dual hAx hx0 (dualFeas_iff.mp hq)
      rw [dotProduct_comm q, dotProduct_comm _ b]
      linarith
  refine ⟨⟨fun hsol => ?_, fun hτ => ⟨_, (key hτ).1⟩⟩, key⟩
  by_contra hτ
  have hτ' : z.τ = 0 := le_antisymm (not_lt.mp hτ) hτ0
  obtain ⟨-, -, hor, hLD, hLP, -⟩ := t3ii_core A b c z hz' hτ'
  rcases hor with h | h
  · exact hLD h (ld_feas_of_opt hsol)
  · obtain ⟨xo, hxo⟩ := hsol
    exact hLP h ⟨xo, hxo.1⟩

lemma pair_opt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xb : Fin n → ℝ) (yb : Fin m → ℝ) (sb : Fin n → ℝ)
    (hx : SelfDualLP.Complexity.LPOptimal A b c xb)
    (hy : SelfDualLP.Complexity.LDOptimal A b c yb sb) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α * (ones n ⬝ᵥ xb + ones n ⬝ᵥ sb + 1) = (n : ℝ) + 1) :
    HLPOptimal7 A b c ⟨α • yb, α • xb, α, 0, α • sb, 0⟩ := by
  have hd := strong_dual hx hy
  obtain ⟨hAx, hx0⟩ := lpFeas_iff.mp hx.1
  obtain ⟨⟨hyf, -⟩, hsb⟩ := hy
  have hyd := dualFeas_iff.mp hyf
  have hsb0 : ∀ j, 0 ≤ sb j := fun j => by rw [hsb]; simp only [Pi.sub_apply]; linarith [hyd j]
  have E1 : A *ᵥ (α • xb) = α • b := by rw [mulVec_smul, hAx]
  have E2 : α • sb = -(Aᵀ *ᵥ (α • yb)) + α • c := by
    rw [hsb, mulVec_smul, smul_sub]; abel
  have E3 : (0 : ℝ) = b ⬝ᵥ (α • yb) - c ⬝ᵥ (α • xb) := by
    simp [dotProduct_smul, hd]
  have E4 := hlp_eq4 A b c (ones n) (ones n) (α • xb) (α • sb) 0 (α • yb) α 0 E1 E2 E3
  have hfeas : HLPFeasible7 A b c ⟨α • yb, α • xb, α, 0, α • sb, 0⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hα0, ?_, le_rfl⟩
    · simp [E1]
    · simp [E2]
    · simp only [mul_zero, add_zero]; exact E3
    · simp only
      rw [E4, ones_dot_ones, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      linear_combination -hα
    · intro j; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hα0 (hx0 j)
    · intro j; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hα0 (hsb0 j)
  refine ⟨hfeas, fun v hv => ?_⟩
  have := hlp_obj A b c (ones n) (ones n) 0 v hv
  simp only [hlpObjective] at this ⊢
  rw [this, mul_zero]
  obtain ⟨-, -, -, -, hvx, hvτ, hvs, hvκ⟩ := hv
  have := dot_nonneg hvx hvs
  have := mul_nonneg hvτ hvκ
  linarith

theorem pair_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ)
    (hx : SelfDualLP.Complexity.LPOptimal A b c xbar)
    (hy : SelfDualLP.Complexity.LDOptimal A b c ybar sbar) :
    0 < ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) ∧
    HLPOptimal7 A b c
      (let α : ℝ := ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1)
       ⟨α • ybar, α • xbar, α, 0, α • sbar, 0⟩) := by
  obtain ⟨hAx, hx0⟩ := lpFeas_iff.mp hx.1
  have hyd := dualFeas_iff.mp hy.1.1
  have hsb0 : ∀ j, 0 ≤ sbar j := fun j => by
    rw [hy.2]; simp only [Pi.sub_apply]; linarith [hyd j]
  have hD : 0 < ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1 := by
    have := dot_nonneg (fun j => (ones_pos j).le) hx0
    have := dot_nonneg (fun j => (ones_pos j).le) hsb0
    linarith
  have hpos : 0 < ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) := by positivity
  exact ⟨hpos, pair_opt A b c xbar ybar sbar hx hy _ hpos.le (by field_simp)⟩

lemma optimal_theta_zero {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {w : HLPPoint m n} (hw : HLPOptimal7 A b c w) : w.θ = 0 := by
  obtain ⟨v, hv, hvθ⟩ := hlp_exists A b c (ones n) (ones n) 0 ones_pos ones_pos
  have h1 := hw.2 v hv
  simp only [hlpObjective, hvθ, mul_zero, ones_dot_ones] at h1
  have h2 := gap_feas7 hw.1
  obtain ⟨-, -, -, -, hx, hτ, hs, hκ⟩ := hw.1
  have := dot_nonneg hx hs
  have := mul_nonneg hτ hκ
  unfold gap at h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem orth_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z w : HLPPoint m n) (hz : HLPFeasible7 A b c z)
    (hw : HLPOptimal7 A b c w) (hκ : w.κ = 0) :
    (z.x - w.x) ⬝ᵥ (z.s - w.s) + (z.τ - w.τ) * (z.κ - w.κ) = 0 ∧
    z.x ⬝ᵥ w.s + z.s ⬝ᵥ w.x + z.κ * w.τ = ((n : ℝ) + 1) * mu z ∧
    ((n : ℝ) + 1) * mu z = ((n : ℝ) + 1) * z.θ := by
  have hθw := optimal_theta_zero hw
  obtain ⟨hez, hLz⟩ := feas7_eqs hz
  obtain ⟨hew, hLw⟩ := feas7_eqs hw.1
  have hcr := cross A b c z w hez hew
  have hgz := gap_feas7 hz
  have hgw := gap_feas7 hw.1
  have hmu := mu_feas7 hz
  rw [hLz, hLw, hθw] at hcr
  rw [hθw] at hgw
  unfold gap at hgz hgw
  rw [hmu]
  refine ⟨?_, ?_, rfl⟩
  · rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hκ]
    rw [hκ] at hcr hgw
    linear_combination hgz + hgw - hcr
  · rw [hκ] at hcr
    rw [dotProduct_comm z.s]
    linear_combination hcr

end LPpart

section RealCore

variable {ι : Type*} [Fintype ι]

lemma posneg_bound (t B : ι → ℝ) (ht : ∑ i, t i = 0) (htB : ∀ i, t i ≤ B i)
    (hB : ∀ i, 0 ≤ B i) : ∑ i, t i ^ 2 ≤ 2 * (∑ i, B i) ^ 2 := by
  have hsq : ∀ i, t i ^ 2 = max (t i) 0 ^ 2 + max (-t i) 0 ^ 2 := by
    intro i
    rcases le_total 0 (t i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hdiff : ∀ i, t i = max (t i) 0 - max (-t i) 0 := by
    intro i
    rcases le_total 0 (t i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hPN : ∑ i, max (t i) 0 = ∑ i, max (-t i) 0 := by
    have : ∑ i, t i = ∑ i, max (t i) 0 - ∑ i, max (-t i) 0 := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => hdiff i)
    linarith
  have hPB : ∑ i, max (t i) 0 ≤ ∑ i, B i :=
    Finset.sum_le_sum (fun i _ => max_le (htB i) (hB i))
  have hP0 : 0 ≤ ∑ i, max (t i) 0 := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have h1 : ∑ i, max (t i) 0 ^ 2 ≤ (∑ i, max (t i) 0) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => le_max_right _ _)
  have h2 : ∑ i, max (-t i) 0 ^ 2 ≤ (∑ i, max (-t i) 0) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => le_max_right _ _)
  rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_add_distrib]
  rw [← hPN] at h2
  nlinarith

lemma single_sq_le (f : ι → ℝ) (i : ι) : f i ^ 2 ≤ ∑ j, f j ^ 2 :=
  Finset.single_le_sum (f := fun j => f j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma corr_real (μ : ℝ) (hμ : 0 < μ) (w t : ι → ℝ) (hdev : ∑ i, (w i - μ) ^ 2 ≤ (μ / 2) ^ 2)
    (hwt : ∀ i, 4 * w i * t i ≤ (μ - w i) ^ 2) (ht : ∑ i, t i = 0) :
    ∑ i, t i ^ 2 ≤ (μ / 4) ^ 2 := by
  have hw : ∀ i, μ / 2 ≤ w i := by
    intro i
    have := le_trans (single_sq_le (fun j => w j - μ) i) hdev
    by_contra h
    push_neg at h
    nlinarith
  have htB : ∀ i, t i ≤ (μ - w i) ^ 2 / (2 * μ) := by
    intro i
    rw [le_div_iff₀ (by linarith)]
    rcases le_or_gt (t i) 0 with h | h
    · nlinarith [sq_nonneg (μ - w i)]
    · nlinarith [hwt i, hw i]
  have hB := posneg_bound t (fun i => (μ - w i) ^ 2 / (2 * μ)) ht htB
    (fun i => div_nonneg (sq_nonneg _) (by linarith))
  have hsumB : ∑ i, (μ - w i) ^ 2 / (2 * μ) ≤ μ / 8 := by
    rw [← Finset.sum_div, div_le_iff₀ (by linarith)]
    have : ∑ i, (μ - w i) ^ 2 = ∑ i, (w i - μ) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    nlinarith
  have hB0 : 0 ≤ ∑ i, (μ - w i) ^ 2 / (2 * μ) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by linarith))
  have : (∑ i, (μ - w i) ^ 2 / (2 * μ)) ^ 2 ≤ (μ / 8) ^ 2 := pow_le_pow_left₀ hB0 hsumB 2
  nlinarith

lemma pred_real (μ : ℝ) (hμ : 0 < μ) (N : ℝ) (w t : ι → ℝ) (hw0 : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = N * μ) (hdev : ∑ i, (w i - μ) ^ 2 ≤ (μ / 4) ^ 2)
    (hwt : ∀ i, 4 * w i * t i ≤ w i ^ 2) (ht : ∑ i, t i = 0) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α ^ 4 * 8 * N ^ 2 ≤ 1) (hα1 : α ≤ 1) (hcase : α ≤ 1 / 2 ∨ ∑ i, t i ^ 2 = 0) :
    ∑ i, ((1 - α) * (w i - μ) + α ^ 2 * t i) ^ 2 ≤ ((1 - α) * μ / 2) ^ 2 := by
  have htB : ∀ i, t i ≤ w i / 4 := by
    intro i
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hwt i, hw0 i]
  have hT := posneg_bound t (fun i => w i / 4) ht htB (fun i => by linarith [hw0 i])
  rw [← Finset.sum_div, hsum] at hT
  set U := ∑ i, ((1 - α) * (w i - μ)) ^ 2 with hU
  set V := ∑ i, (α ^ 2 * t i) ^ 2 with hV
  set C := ∑ i, ((1 - α) * (w i - μ)) * (α ^ 2 * t i) with hC
  have hexp : ∑ i, ((1 - α) * (w i - μ) + α ^ 2 * t i) ^ 2 = U + 2 * C + V := by
    rw [hU, hV, hC, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hCS : C ^ 2 ≤ U * V := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hUe : U = (1 - α) ^ 2 * ∑ i, (w i - μ) ^ 2 := by
    rw [hU, Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hVe : V = α ^ 4 * ∑ i, t i ^ 2 := by
    rw [hV, Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hUb : U ≤ ((1 - α) * μ / 4) ^ 2 := by
    rw [hUe]
    have : (1 - α) ^ 2 * ∑ i, (w i - μ) ^ 2 ≤ (1 - α) ^ 2 * (μ / 4) ^ 2 :=
      mul_le_mul_of_nonneg_left hdev (sq_nonneg _)
    nlinarith
  rw [hexp]
  rcases hcase with h | h
  · have hVb : V ≤ (μ / 8) ^ 2 := by
      rw [hVe]
      have h4 : 0 ≤ α ^ 4 := by positivity
      have : α ^ 4 * ∑ i, t i ^ 2 ≤ α ^ 4 * (2 * (N * μ / 4) ^ 2) :=
        mul_le_mul_of_nonneg_left hT h4
      nlinarith
    set a := (1 - α) * μ / 4 with ha
    set bb := μ / 8 with hbb
    have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg (mul_nonneg (by linarith) hμ.le); norm_num
    have hbb0 : 0 ≤ bb := by rw [hbb]; positivity
    have hab : bb ≤ a := by rw [ha, hbb]; nlinarith
    have hUV : U * V ≤ (a * bb) ^ 2 := by
      have := mul_le_mul hUb hVb hV0 (sq_nonneg _)
      nlinarith
    have hCab : C ≤ a * bb := by
      by_contra hc
      push_neg at hc
      have hpos : 0 ≤ a * bb := mul_nonneg ha0 hbb0
      nlinarith
    have : ((1 - α) * μ / 2) ^ 2 = (2 * a) ^ 2 := by rw [ha]; ring
    rw [this]
    nlinarith
  · have hV0' : V = 0 := by rw [hVe, h, mul_zero]
    have hC0 : C = 0 := by
      rw [hV0', mul_zero] at hCS
      nlinarith [sq_nonneg C]
    rw [hV0', hC0]
    have : ((1 - α) * μ / 4) ^ 2 ≤ ((1 - α) * μ / 2) ^ 2 := by nlinarith [sq_nonneg ((1 - α) * μ)]
    linarith

lemma pos_pair (x s a b' : ℝ) (hx : 0 < x) (hs : 0 < s) (hp : 0 < (x + a) * (s + b'))
    (hw : 0 < x * (s + b') + s * (x + a)) : 0 < x + a ∧ 0 < s + b' := by
  rcases lt_or_ge 0 (x + a) with h1 | h1
  · rcases lt_or_ge 0 (s + b') with h2 | h2
    · exact ⟨h1, h2⟩
    · nlinarith
  · rcases lt_or_ge 0 (s + b') with h2 | h2
    · nlinarith
    · nlinarith

end RealCore

section NbhdPart

variable {m n : ℕ}

def Wv (z : HLPPoint m n) : Option (Fin n) → ℝ :=
  fun o => Option.elim o (z.τ * z.κ) (fun j => z.x j * z.s j)

def Tv (d : HLPPoint m n) : Option (Fin n) → ℝ :=
  fun o => Option.elim o (d.τ * d.κ) (fun j => d.x j * d.s j)

lemma sum_Wv (z : HLPPoint m n) : ∑ o, Wv z o = gap z := by
  rw [Fintype.sum_option]; simp only [Wv, Option.elim, gap, dotProduct]; ring

lemma dev_eq (z : HLPPoint m n) :
    centralityDeviation z = Real.sqrt (∑ o, (Wv z o - mu z) ^ 2) := by
  unfold centralityDeviation
  rw [Fintype.sum_option]
  simp only [Wv, Option.elim]
  rw [add_comm]

lemma W_move {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    {γ : ℝ} (hd : IsPCDirection A b c z d γ) (α : ℝ) (o : Option (Fin n)) :
    Wv (z.move d α) o = Wv z o + α * (γ * mu z - Wv z o) + α ^ 2 * Tv d o := by
  cases o with
  | none =>
    simp only [Wv, Tv, Option.elim, HLPPoint.move]
    linear_combination α * hd.2.2
  | some j =>
    simp only [Wv, Tv, Option.elim, HLPPoint.move, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination α * hd.2.1 j

lemma sum_Tv {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {d : HLPPoint m n}
    (hd : InQ7 A b c d) : ∑ o, Tv d o = 0 := by
  rw [Fintype.sum_option]
  have := gap_dir hd
  simp only [Tv, Option.elim, gap, dotProduct] at this ⊢
  linarith

lemma amgm {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    {γ : ℝ} (hd : IsPCDirection A b c z d γ) (o : Option (Fin n)) :
    4 * Wv z o * Tv d o ≤ (γ * mu z - Wv z o) ^ 2 := by
  cases o with
  | none =>
    simp only [Wv, Tv, Option.elim]
    rw [← hd.2.2]
    nlinarith [sq_nonneg (z.τ * d.κ - z.κ * d.τ)]
  | some j =>
    simp only [Wv, Tv, Option.elim]
    rw [← hd.2.1 j]
    nlinarith [sq_nonneg (z.x j * d.s j - z.s j * d.x j)]

lemma mu_move {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z d : HLPPoint m n}
    {γ : ℝ} (hd : IsPCDirection A b c z d γ) (α : ℝ) :
    mu (z.move d α) = (1 + α * (γ - 1)) * mu z := by
  unfold mu; rw [gap_move_pc hd]; ring

lemma mu_pos_of {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    (hz : HLPStrictlyFeasible7 A b c z) : 0 < mu z := by
  obtain ⟨-, hx, hτ, hs, hκ⟩ := hz
  unfold mu; exact div_pos (gap_pos_of_pos hx hτ hs hκ) (by positivity)

lemma Wv_pos {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    (hz : HLPStrictlyFeasible7 A b c z) (o : Option (Fin n)) : 0 < Wv z o := by
  obtain ⟨-, hx, hτ, hs, hκ⟩ := hz
  cases o with
  | none => exact mul_pos hτ hκ
  | some j => exact mul_pos (hx j) (hs j)

lemma nbhd_sq {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    {β : ℝ} (hz : Nbhd A b c β z) : ∑ o, (Wv z o - mu z) ^ 2 ≤ (β * mu z) ^ 2 := by
  obtain ⟨-, h⟩ := hz
  rw [dev_eq] at h
  have h0 : 0 ≤ ∑ o, (Wv z o - mu z) ^ 2 := Finset.sum_nonneg (fun o _ => sq_nonneg _)
  have h1 := Real.sq_sqrt h0
  have h2 := Real.sqrt_nonneg (∑ o, (Wv z o - mu z) ^ 2)
  nlinarith

lemma nbhd_mono {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {z : HLPPoint m n}
    {β β' : ℝ} (hz : Nbhd A b c β z) (hβ : β ≤ β') : Nbhd A b c β' z := by
  refine ⟨hz.1, le_trans hz.2 ?_⟩
  have := mu_pos_of hz.1
  nlinarith

theorem nbhd_of_move {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {z d : HLPPoint m n} {γ : ℝ}
    (hz : HLPStrictlyFeasible7 A b c z) (hd : IsPCDirection A b c z d γ) (α β' : ℝ)
    (hβ0 : 0 ≤ β') (hβ1 : β' < 1) (hfac : 0 < 1 + α * (γ - 1))
    (hws : ∀ o, 0 < 2 * Wv z o + α * (γ * mu z - Wv z o))
    (hdev : ∑ o, (Wv z o + α * (γ * mu z - Wv z o) + α ^ 2 * Tv d o -
      (1 + α * (γ - 1)) * mu z) ^ 2 ≤ (β' * ((1 + α * (γ - 1)) * mu z)) ^ 2) :
    Nbhd A b c β' (z.move d α) := by
  have hμ := mu_pos_of hz
  obtain ⟨hf, hx, hτ, hs, hκ⟩ := hz
  have hμ' : 0 < mu (z.move d α) := by rw [mu_move hd]; exact mul_pos hfac hμ
  have hdev' : ∑ o, (Wv (z.move d α) o - mu (z.move d α)) ^ 2 ≤
      (β' * mu (z.move d α)) ^ 2 := by
    rw [mu_move hd]; simp only [W_move hd]; exact hdev
  have hprod : ∀ o, 0 < Wv (z.move d α) o := by
    intro o
    have h1 := le_trans (single_sq_le (fun o => Wv (z.move d α) o - mu (z.move d α)) o) hdev'
    by_contra h
    push_neg at h
    have h2 : mu (z.move d α) ^ 2 ≤ (Wv (z.move d α) o - mu (z.move d α)) ^ 2 := by nlinarith
    have h3 : (β' * mu (z.move d α)) ^ 2 < mu (z.move d α) ^ 2 := by
      have : β' * mu (z.move d α) < mu (z.move d α) := by nlinarith
      have h4 : 0 ≤ β' * mu (z.move d α) := mul_nonneg hβ0 hμ'.le
      nlinarith
    linarith
  have hposx : ∀ j, 0 < (z.move d α).x j ∧ 0 < (z.move d α).s j := by
    intro j
    have h1 := hprod (some j)
    have h2 := hws (some j)
    simp only [Wv, Option.elim, HLPPoint.move, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    refine pos_pair _ _ _ _ (hx j) (hs j) h1 ?_
    have e : z.x j * (z.s j + α * d.s j) + z.s j * (z.x j + α * d.x j) =
        2 * (z.x j * z.s j) + α * (γ * mu z - z.x j * z.s j) := by
      linear_combination α * hd.2.1 j
    rw [e]; exact h2
  have hposτ : 0 < (z.move d α).τ ∧ 0 < (z.move d α).κ := by
    have h1 := hprod none
    have h2 := hws none
    simp only [Wv, Option.elim, HLPPoint.move] at h1 h2 ⊢
    refine pos_pair _ _ _ _ hτ hκ h1 ?_
    have e : z.τ * (z.κ + α * d.κ) + z.κ * (z.τ + α * d.τ) =
        2 * (z.τ * z.κ) + α * (γ * mu z - z.τ * z.κ) := by
      linear_combination α * hd.2.2
    rw [e]; exact h2
  obtain ⟨he, hL⟩ := feas7_eqs hf
  obtain ⟨hed, hLd⟩ := inQ7_eqs hd.1
  have hem := eqs_move he hed α
  have hLm : Lres A b c (z.move d α) = -(n : ℝ) - 1 := by rw [Lres_move, hL, hLd]; ring
  refine ⟨⟨⟨hem.1, hem.2.1, hem.2.2, ?_, fun j => (hposx j).1.le, hposτ.1.le,
    fun j => (hposx j).2.le, hposτ.2.le⟩, fun j => (hposx j).1, hposτ.1,
    fun j => (hposx j).2, hposτ.2⟩, ?_⟩
  · rw [ones_dot_ones]; exact hLm
  · rw [dev_eq]
    calc Real.sqrt (∑ o, (Wv (z.move d α) o - mu (z.move d α)) ^ 2)
        ≤ Real.sqrt ((β' * mu (z.move d α)) ^ 2) := Real.sqrt_le_sqrt hdev'
      _ = β' * mu (z.move d α) := Real.sqrt_sq (mul_nonneg hβ0 hμ'.le)

lemma ratio_eq {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {z z' : HLPPoint m n} (hz : HLPFeasible7 A b c z) (hz' : HLPFeasible7 A b c z') :
    z'.θ / z.θ = gap z' / gap z := by
  rw [gap_feas7 hz, gap_feas7 hz', mul_div_mul_left _ _ (by positivity)]

theorem corr_core {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    (z d : HLPPoint m n) (hz : Nbhd A b c (1 / 2) z) (hd : IsPCDirection A b c z d 1) :
    Nbhd A b c (1 / 4) (z.move d 1) ∧
    (z.move d 1).θ / z.θ = gap (z.move d 1) / gap z ∧
    gap (z.move d 1) / gap z = 1 := by
  have hμ := mu_pos_of hz.1
  have hN : Nbhd A b c (1 / 4) (z.move d 1) := by
    apply nbhd_of_move hz.1 hd 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    · intro o; have := Wv_pos hz.1 o; nlinarith
    · have e1 : ∀ o, Wv z o + 1 * (1 * mu z - Wv z o) + 1 ^ 2 * Tv d o -
          (1 + 1 * (1 - 1)) * mu z = Tv d o := fun o => by ring
      simp only [e1]
      have e2 : (1 / 4 * ((1 + 1 * (1 - 1)) * mu z)) ^ 2 = (mu z / 4) ^ 2 := by ring
      rw [e2]
      apply corr_real (mu z) hμ (Wv z) (Tv d)
      · have := nbhd_sq hz
        have e3 : (1 / 2 * mu z) ^ 2 = (mu z / 2) ^ 2 := by ring
        rw [e3] at this; exact this
      · intro o; have := amgm hd o; rw [one_mul] at this; exact this
      · exact sum_Tv hd.1
  have hg : gap (z.move d 1) = gap z := by rw [gap_move_pc hd]; ring
  have hgpos : 0 < gap z := by
    obtain ⟨-, hx, hτ, hs, hκ⟩ := hz.1; exact gap_pos_of_pos hx hτ hs hκ
  refine ⟨hN, ratio_eq hz.1.1 hN.1.1, ?_⟩
  rw [hg, div_self hgpos.ne']

theorem pred_nbhd {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    (z d : HLPPoint m n) (hz : Nbhd A b c (1 / 4) z) (hd : IsPCDirection A b c z d 0)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α ^ 4 * 8 * ((n : ℝ) + 1) ^ 2 ≤ 1) :
    Nbhd A b c (1 / 2) (z.move d α) := by
  have hμ := mu_pos_of hz.1
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hα4 : α ^ 4 ≤ 1 / 8 := by nlinarith [pow_nonneg hα0 4]
  have hα1 : α < 1 := by
    by_contra h
    push_neg at h
    have h2 : 1 ≤ α ^ 2 := by nlinarith
    have h4 : 1 ≤ α ^ 4 := by nlinarith
    linarith
  apply nbhd_of_move hz.1 hd α (1 / 2) (by norm_num) (by norm_num) (by linarith)
  · intro o; have := Wv_pos hz.1 o; nlinarith
  · have e1 : ∀ o, Wv z o + α * (0 * mu z - Wv z o) + α ^ 2 * Tv d o -
        (1 + α * (0 - 1)) * mu z = (1 - α) * (Wv z o - mu z) + α ^ 2 * Tv d o := fun o => by ring
    simp only [e1]
    have e2 : (1 / 2 * ((1 + α * (0 - 1)) * mu z)) ^ 2 = ((1 - α) * mu z / 2) ^ 2 := by ring
    rw [e2]
    have hcase : α ≤ 1 / 2 ∨ ∑ o, Tv d o ^ 2 = 0 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · right
        subst hn
        have h := sum_Tv hd.1
        rw [Fintype.sum_option] at h ⊢
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h ⊢
        rw [h]; ring
      · left
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have h4 : (4 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
        have : α ^ 4 ≤ 1 / 32 := by nlinarith [pow_nonneg hα0 4]
        by_contra h
        push_neg at h
        have h2 : 1 / 4 < α ^ 2 := by nlinarith
        have h3 : 1 / 16 < α ^ 4 := by nlinarith
        linarith
    apply pred_real (mu z) hμ ((n : ℝ) + 1) (Wv z) (Tv d) (Wv_pos hz.1)
    · rw [sum_Wv]; unfold mu; field_simp
    · have := nbhd_sq hz
      have e3 : (1 / 4 * mu z) ^ 2 = (mu z / 4) ^ 2 := by ring
      rw [e3] at this; exact this
    · intro o; have := amgm hd o; rw [zero_mul, zero_sub, neg_sq] at this; exact this
    · exact sum_Tv hd.1
    · exact hα0
    · exact hα
    · exact hα1.le
    · exact hcase

theorem pred_core {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    (z d : HLPPoint m n) (αbar : ℝ)
    (hz : Nbhd A b c (1 / 4) z) (hd : IsPCDirection A b c z d 0)
    (hα : IsGreatest {a : ℝ | Nbhd A b c (1 / 2) (z.move d a)} αbar) :
    Nbhd A b c (1 / 2) (z.move d αbar) ∧
    (z.move d αbar).θ / z.θ = gap (z.move d αbar) / gap z ∧
    gap (z.move d αbar) / gap z ≤ 1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt ((n : ℝ) + 1) := by
  set α0 := (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt ((n : ℝ) + 1) with hα0
  have hα0nn : 0 ≤ α0 := by rw [hα0]; positivity
  have h8 : ((8 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num [Real.rpow_neg_one]
  have hs4 : (Real.sqrt ((n : ℝ) + 1)) ^ 4 = ((n : ℝ) + 1) ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    calc (Real.sqrt ((n : ℝ) + 1)) ^ 4 = ((Real.sqrt ((n : ℝ) + 1)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]
  have hα04 : α0 ^ 4 * 8 * ((n : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [hα0, div_pow, h8, hs4]
    have : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    field_simp
    rfl
  have hmem : α0 ∈ {a : ℝ | Nbhd A b c (1 / 2) (z.move d a)} :=
    pred_nbhd z d hz hd α0 hα0nn hα04
  have hle : α0 ≤ αbar := hα.2 hmem
  have hN : Nbhd A b c (1 / 2) (z.move d αbar) := hα.1
  have hgpos : 0 < gap z := by
    obtain ⟨-, hx, hτ, hs, hκ⟩ := hz.1; exact gap_pos_of_pos hx hτ hs hκ
  refine ⟨hN, ratio_eq hz.1.1 hN.1.1, ?_⟩
  rw [gap_move_pc hd, mul_div_assoc, div_self hgpos.ne']
  linarith

end NbhdPart

section Extra1
variable {m n : ℕ}

theorem t2ii_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    HLPStrictlyFeasible A b c x0 y0 s0 ⟨y0, x0, 1, 1, s0, 1⟩ := by
  refine ⟨⟨?_, ?_, ?_, ?_, fun j => (hx0 j).le, zero_le_one, fun j => (hs0 j).le, zero_le_one⟩,
    hx0, one_pos, hs0, one_pos⟩
  · simp only [bbar, one_smul]; abel
  · simp only [cbar, one_smul]; abel
  · simp only [zbar]; ring
  · simp only [bbar, cbar, zbar, sub_dotProduct, dotProduct_sub]
    have h := dot_mulVec_transpose A x0 y0
    rw [dotProduct_comm (Aᵀ *ᵥ y0) x0, ← h, dotProduct_comm (A *ᵥ x0) y0,
      dotProduct_comm s0 x0, dotProduct_comm c x0, dotProduct_comm b y0]
    ring

theorem t5ii_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : HLPPoint m n) (hd : InQ7 A b c d) :
    d.x ⬝ᵥ d.s + d.τ * d.κ = 0 := gap_dir hd

end Extra1

end SelfDualLP.Complexity

open SelfDualLP.Complexity


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) :
    (LPHasSolution A b c ↔ 0 < z.τ) ∧
    (0 < z.τ → LPOptimal A b c (z.τ⁻¹ • z.x) ∧ LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s)) := by
  exact t3i_core A b c z hz
