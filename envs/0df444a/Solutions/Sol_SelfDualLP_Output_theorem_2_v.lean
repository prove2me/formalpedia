-- Prove2me | solution 1 for SelfDualLP.Output.theorem_2_v
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:14:35.040526+00:00
-- url     : https://prove2.me/submissions/b0f9f87c-d498-4ad0-806a-5f3ed4a787ae

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix


namespace SelfDualLP.Output


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

section GTpart

variable {m n : ℕ}

/-- Homogeneous HLP point with `θ = 0` and nonnegative sign-constrained variables. -/
def Hom (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (u : HLPPoint m n) : Prop :=
  A *ᵥ u.x = u.τ • b ∧ u.s = -(Aᵀ *ᵥ u.y) + u.τ • c ∧ u.κ = b ⬝ᵥ u.y - c ⬝ᵥ u.x ∧ u.θ = 0 ∧
  (∀ j, 0 ≤ u.x j) ∧ 0 ≤ u.τ ∧ (∀ j, 0 ≤ u.s j) ∧ 0 ≤ u.κ

lemma hom_gap {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {u : HLPPoint m n}
    (hu : Hom A b c u) : u.x ⬝ᵥ u.s + u.τ * u.κ = 0 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hu
  have e1 : A *ᵥ u.x - u.τ • b + u.θ • (0 : Fin m → ℝ) = 0 := by rw [h1]; simp
  have e2 : u.s = -(Aᵀ *ᵥ u.y) + u.τ • c - u.θ • (0 : Fin n → ℝ) := by rw [h2]; simp
  have e3 : u.κ = b ⬝ᵥ u.y - c ⬝ᵥ u.x + 0 * u.θ := by rw [h3]; ring
  have := cross_gen A b 0 c 0 0 u u e1 e2 e3 e1 e2 e3
  rw [h4] at this
  linarith

lemma hom_add {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {u v : HLPPoint m n}
    (hu : Hom A b c u) (hv : Hom A b c v) : Hom A b c (u.move v 1) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hu
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [HLPPoint.move, one_smul, one_mul]
  · rw [mulVec_add, u1, v1, add_smul]
  · rw [u2, v2, mulVec_add, add_smul]; abel
  · rw [u3, v3, dotProduct_add, dotProduct_add]; ring
  · rw [u4, v4]; ring
  · intro j; simp only [Pi.add_apply]; linarith [u5 j, v5 j]
  · linarith
  · intro j; simp only [Pi.add_apply]; linarith [u7 j, v7 j]
  · linarith

lemma hom_smul {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {u : HLPPoint m n}
    (hu : Hom A b c u) (l : ℝ) (hl : 0 ≤ l) : Hom A b c (u.smul l) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [HLPPoint.smul]
  · rw [mulVec_smul, u1, smul_smul]
  · rw [u2, mulVec_smul, smul_add, smul_neg, smul_smul]
  · rw [u3, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  · rw [u4]; ring
  · intro j; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hl (u5 j)
  · exact mul_nonneg hl u6
  · intro j; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hl (u7 j)
  · exact mul_nonneg hl u8

noncomputable def gtCol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c wv : Fin n → ℝ)
    (wt : ℝ) : ColI m n → (RowI m n → ℝ) :=
  Sum.elim
    (fun i => Sum.elim (fun _ => 0) (Sum.elim (fun j => A i j) (Sum.elim (fun _ => -b i) (fun _ => 0))))
    (Sum.elim
      (fun i => Sum.elim (fun _ => 0) (Sum.elim (fun j => -A i j) (Sum.elim (fun _ => b i) (fun _ => 0))))
      (Sum.elim
        (fun j => Sum.elim (fun i => A i j) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => c j) (fun _ => wv j))))
        (Sum.elim
          (fun _ => Sum.elim (fun i => -b i) (Sum.elim (fun j => -c j) (Sum.elim (fun _ => 0) (fun _ => wt))))
          (Sum.elim
            (fun j => Sum.elim (fun _ => 0) (Sum.elim (fun j' => if j' = j then 1 else 0) (Sum.elim (fun _ => 0) (fun _ => wv j))))
            (fun _ => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => wt))))))))

noncomputable def gtM (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c wv : Fin n → ℝ) (wt : ℝ) :
    Matrix (RowI m n) (ColI m n) ℝ :=
  Matrix.of fun r k => gtCol A b c wv wt k r

lemma gt_exists (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c wv : Fin n → ℝ) (wt : ℝ)
    (hwv : ∀ j, 0 ≤ wv j) (hwt : 0 ≤ wt)
    (hno : ∀ u : HLPPoint m n, Hom A b c u → (∀ k, wv k ≤ u.x k) → (∀ k, wv k ≤ u.s k) →
      wt ≤ u.τ → wt ≤ u.κ → False) :
    ∃ u : HLPPoint m n, Hom A b c u ∧ wv ⬝ᵥ u.x + wv ⬝ᵥ u.s + wt * u.τ + wt * u.κ = 1 := by
  have hcone : Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) 1 ∈ LPB.cone (gtM A b c wv wt) := by
    by_contra hnot
    obtain ⟨yv, hy, hyt⟩ := LPB.farkas _ _ hnot
    set p : Fin m → ℝ := fun i => yv (Sum.inl i) with hp
    set q : Fin n → ℝ := fun j => yv (Sum.inr (Sum.inl j)) with hq
    set r : ℝ := yv (Sum.inr (Sum.inr (Sum.inl ()))) with hr
    set ρ : ℝ := yv (Sum.inr (Sum.inr (Sum.inr ()))) with hρ
    have hρneg : ρ < 0 := by
      have : yv ⬝ᵥ Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) (1 : ℝ) = ρ := by
        simp [dotProduct_single, hρ]
      rw [this] at hyt; exact hyt
    have col : ∀ k, (yv ᵥ* gtM A b c wv wt) k = yv ⬝ᵥ gtCol A b c wv wt k := by
      intro k; simp [vecMul, dotProduct, gtM]
    have hyp : ∀ i, 0 ≤ ∑ j, q j * A i j - r * b i := by
      intro i
      have := hy (Sum.inl i)
      rw [col] at this
      simpa [dotProduct, gtCol, Fintype.sum_sum_type, hq, hr, mul_comm] using this
    have hym : ∀ i, 0 ≤ -(∑ j, q j * A i j) + r * b i := by
      intro i
      have := hy (Sum.inr (Sum.inl i))
      rw [col] at this
      simpa [dotProduct, gtCol, Fintype.sum_sum_type, hq, hr, mul_comm, Finset.sum_neg_distrib]
        using this
    have hx : ∀ j, 0 ≤ ∑ i, p i * A i j + r * c j + ρ * wv j := by
      intro j
      have := hy (Sum.inr (Sum.inr (Sum.inl j)))
      rw [col] at this
      simp [dotProduct, gtCol, Fintype.sum_sum_type, hp, hr, hρ, mul_comm] at this ⊢
      linarith
    have hτ : 0 ≤ -(∑ i, p i * b i) - ∑ j, q j * c j + ρ * wt := by
      have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
      rw [col] at this
      simp [dotProduct, gtCol, Fintype.sum_sum_type, hp, hq, hρ, mul_comm, Finset.sum_neg_distrib,
        sub_eq_add_neg] at this ⊢
      linarith
    have hs : ∀ j, 0 ≤ q j + ρ * wv j := by
      intro j
      have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
      rw [col] at this
      simpa [dotProduct, gtCol, Fintype.sum_sum_type, hq, hρ, mul_comm] using this
    have hκ : 0 ≤ r + ρ * wt := by
      have := hy (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
      rw [col] at this
      simpa [dotProduct, gtCol, Fintype.sum_sum_type, hr, hρ, mul_comm] using this
    have hAq : ∀ i, ∑ j, q j * A i j = r * b i := fun i =>
      le_antisymm (by linarith [hym i]) (by linarith [hyp i])
    -- the certificate point
    let u : HLPPoint m n := ⟨-p, q, r, 0, Aᵀ *ᵥ p + r • c, -(b ⬝ᵥ p) - c ⬝ᵥ q⟩
    have hsj : ∀ j, (Aᵀ *ᵥ p + r • c) j = ∑ i, p i * A i j + r * c j := by
      intro j; simp [mulVec, dotProduct, mul_comm]
    have hu : Hom A b c u := by
      refine ⟨?_, ?_, ?_, rfl, fun j => ?_, ?_, fun j => ?_, ?_⟩
      · funext i
        have := hAq i
        simp only [Pi.smul_apply, smul_eq_mul, u]
        simp only [mulVec, dotProduct]
        rw [← this]; exact Finset.sum_congr rfl (fun j _ => by ring)
      · simp [u, mulVec_neg]
      · simp only [u, dotProduct_neg]
      · simp only [u]; nlinarith [hs j, hwv j]
      · simp only [u]; nlinarith
      · simp only [u]; rw [hsj]; nlinarith [hx j, hwv j]
      · simp only [u]
        have e1 : b ⬝ᵥ p = ∑ i, p i * b i := by simp [dotProduct, mul_comm]
        have e2 : c ⬝ᵥ q = ∑ j, q j * c j := by simp [dotProduct, mul_comm]
        rw [e1, e2]; nlinarith
    -- scale it by 1/(-ρ)
    have hl : 0 ≤ (-ρ)⁻¹ := inv_nonneg.mpr (by linarith)
    apply hno (u.smul (-ρ)⁻¹) (hom_smul hu _ hl)
    · intro k
      simp only [HLPPoint.smul, Pi.smul_apply, smul_eq_mul, u]
      rw [le_inv_mul_iff₀ (by linarith)]
      nlinarith [hs k]
    · intro k
      simp only [HLPPoint.smul, Pi.smul_apply, smul_eq_mul, u]
      rw [le_inv_mul_iff₀ (by linarith), hsj]
      nlinarith [hx k]
    · simp only [HLPPoint.smul, u]
      rw [le_inv_mul_iff₀ (by linarith)]
      nlinarith
    · simp only [HLPPoint.smul, u]
      rw [le_inv_mul_iff₀ (by linarith)]
      have e1 : b ⬝ᵥ p = ∑ i, p i * b i := by simp [dotProduct, mul_comm]
      have e2 : c ⬝ᵥ q = ∑ j, q j * c j := by simp [dotProduct, mul_comm]
      rw [e1, e2]; nlinarith
  obtain ⟨z, hz, hMz⟩ := hcone
  have hrow : ∀ r, ∑ k, gtCol A b c wv wt k r * z k =
      (Pi.single (Sum.inr (Sum.inr (Sum.inr ()))) (1 : ℝ) : RowI m n → ℝ) r := by
    intro r
    have := congrFun hMz r
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, gtM] using this
  set X : Fin n → ℝ := fun j => z (Sum.inr (Sum.inr (Sum.inl j))) with hX
  set Y : Fin m → ℝ := fun i => z (Sum.inl i) - z (Sum.inr (Sum.inl i)) with hY
  set T : ℝ := z (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) with hT
  set S : Fin n → ℝ := fun j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) with hS
  set K : ℝ := z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))) with hK
  have E1 : A *ᵥ X = T • b := by
    funext i
    have := hrow (Sum.inl i)
    simp [gtCol, Fintype.sum_sum_type] at this
    simp [Matrix.mulVec, dotProduct, hX, hT, mul_comm]
    linarith
  have E2 : S = -(Aᵀ *ᵥ Y) + T • c := by
    funext j
    have := hrow (Sum.inr (Sum.inl j))
    simp [gtCol, Fintype.sum_sum_type] at this
    simp [Matrix.mulVec, dotProduct, hY, hT, hS, mul_comm, mul_sub, Finset.sum_sub_distrib]
    linarith
  have E3 : K = b ⬝ᵥ Y - c ⬝ᵥ X := by
    have := hrow (Sum.inr (Sum.inr (Sum.inl ())))
    simp [gtCol, Fintype.sum_sum_type] at this
    simp [dotProduct, hY, hX, hK, mul_sub, Finset.sum_sub_distrib]
    linarith
  have E4 : wv ⬝ᵥ X + wv ⬝ᵥ S + wt * T + wt * K = 1 := by
    have := hrow (Sum.inr (Sum.inr (Sum.inr ())))
    simp [gtCol, Fintype.sum_sum_type] at this
    simp [dotProduct, hX, hS, hT, hK] at this ⊢
    linarith
  exact ⟨⟨Y, X, T, 0, S, K⟩, ⟨E1, E2, E3, rfl, fun j => hz _, hz _, fun j => hz _, hz _⟩, E4⟩

lemma coord_point (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (o : Option (Fin n)) :
    ∃ u : HLPPoint m n, Hom A b c u ∧
      Option.elim o (0 < u.τ + u.κ) (fun j => 0 < u.x j + u.s j) := by
  cases o with
  | none =>
    obtain ⟨u, hu, h1⟩ := gt_exists A b c 0 1 (fun _ => le_rfl) zero_le_one (by
      intro u hu _ _ hτ hκ
      have := hom_gap hu
      obtain ⟨-, -, -, -, hx, -, hs, -⟩ := hu
      have := dot_nonneg hx hs
      nlinarith)
    refine ⟨u, hu, ?_⟩
    simp only [Option.elim]
    simp at h1
    linarith
  | some j =>
    obtain ⟨u, hu, h1⟩ := gt_exists A b c (fun k => if k = j then 1 else 0) 0
      (fun k => by split_ifs <;> norm_num) le_rfl (by
      intro u hu hx' hs' _ _
      have hg := hom_gap hu
      obtain ⟨-, -, -, -, hx, hτ, hs, hκ⟩ := hu
      have h1 := hx' j
      have h2 := hs' j
      simp only [if_true] at h1 h2
      have h3 : u.x j * u.s j ≤ u.x ⬝ᵥ u.s :=
        Finset.single_le_sum (f := fun k => u.x k * u.s k)
          (fun k _ => mul_nonneg (hx k) (hs k)) (Finset.mem_univ j)
      have := mul_nonneg hτ hκ
      nlinarith)
    refine ⟨u, hu, ?_⟩
    simp only [Option.elim]
    simp [dotProduct] at h1
    linarith

lemma all_coords (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S : Finset (Option (Fin n))) :
    ∃ u : HLPPoint m n, Hom A b c u ∧
      ∀ o ∈ S, Option.elim o (0 < u.τ + u.κ) (fun j => 0 < u.x j + u.s j) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨0, 0, 0, 0, 0, 0⟩, ⟨by simp, by simp, by simp, rfl, fun _ => le_rfl, le_rfl,
      fun _ => le_rfl, le_rfl⟩, by simp⟩
  | insert o S ho ih =>
    obtain ⟨u, hu, hS⟩ := ih
    obtain ⟨v, hv, ho'⟩ := coord_point A b c o
    refine ⟨u.move v 1, hom_add hu hv, ?_⟩
    obtain ⟨-, -, -, -, ux, uτ, us, uκ⟩ := hu
    obtain ⟨-, -, -, -, vx, vτ, vs, vκ⟩ := hv
    intro o' ho''
    rcases Finset.mem_insert.mp ho'' with h | h
    · subst h
      cases o' with
      | none =>
        simp only [Option.elim, HLPPoint.move, one_mul] at ho' ⊢; linarith
      | some j =>
        simp only [Option.elim, HLPPoint.move, Pi.add_apply, Pi.smul_apply, one_smul] at ho' ⊢
        linarith [ux j, us j]
    · have := hS o' h
      cases o' with
      | none =>
        simp only [Option.elim, HLPPoint.move, one_mul] at this ⊢; linarith
      | some j =>
        simp only [Option.elim, HLPPoint.move, Pi.add_apply, Pi.smul_apply, one_smul] at this ⊢
        linarith [vx j, vs j]

theorem t2v_core (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    ∃ z : HLPPoint m n, StrictlySelfComplementary A b c x0 y0 s0 z := by
  obtain ⟨u, hu, hpos⟩ := all_coords A b c Finset.univ
  have hτκ : 0 < u.τ + u.κ := hpos none (Finset.mem_univ _)
  have hxs : ∀ j, 0 < u.x j + u.s j := fun j => hpos (some j) (Finset.mem_univ _)
  obtain ⟨u1, u2, u3, u4, ux, uτ, us, uκ⟩ := hu
  set Nn := x0 ⬝ᵥ u.s + s0 ⬝ᵥ u.x + u.τ + u.κ with hNn
  have hN : 0 < Nn := by
    have := dot_nonneg (fun j => (hx0 j).le) us
    have := dot_nonneg (fun j => (hs0 j).le) ux
    linarith
  have hP : 0 < x0 ⬝ᵥ s0 + 1 := by
    have := dot_nonneg (fun j => (hx0 j).le) (fun j => (hs0 j).le); linarith
  set l := (x0 ⬝ᵥ s0 + 1) / Nn with hl
  have hl0 : 0 < l := div_pos hP hN
  have hw := hom_smul ⟨u1, u2, u3, u4, ux, uτ, us, uκ⟩ l hl0.le
  obtain ⟨w1, w2, w3, w4, wx, wτ, ws, wκ⟩ := hw
  have E4 := hlp_eq4 A b c x0 s0 (u.smul l).x (u.smul l).s y0 (u.smul l).y (u.smul l).τ
    (u.smul l).κ w1 w2 w3
  have hfeas : HLPFeasible A b c x0 y0 s0 (u.smul l) := by
    refine ⟨?_, ?_, ?_, ?_, wx, wτ, ws, wκ⟩
    · rw [w1, w4]; simp
    · rw [w4]; simpa using w2
    · rw [w4]; simpa using w3
    · rw [E4]
      simp only [HLPPoint.smul, dotProduct_smul, smul_eq_mul]
      have : l * Nn = x0 ⬝ᵥ s0 + 1 := by rw [hl]; field_simp
      rw [hNn] at this
      linarith
  refine ⟨u.smul l, ⟨hfeas, fun v hv => ?_⟩, w4, fun j => ?_, ?_⟩
  · have h0 : hlpObjective x0 s0 (u.smul l) = 0 := by simp [hlpObjective, w4]
    rw [h0, hlp_obj A b c x0 s0 y0 v hv]
    obtain ⟨-, -, -, -, hx, hτ, hs, hκ⟩ := hv
    have := dot_nonneg hx hs
    have := mul_nonneg hτ hκ
    linarith
  · simp only [HLPPoint.smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_add]; exact mul_pos hl0 (hxs j)
  · simp only [HLPPoint.smul]
    rw [← mul_add]; exact mul_pos hl0 hτκ

end GTpart
end SelfDualLP.Output

open SelfDualLP.Output


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    ∃ z : HLPPoint m n, StrictlySelfComplementary A b c x0 y0 s0 z := by
  exact t2v_core A b c x0 y0 s0 hx0 hs0
