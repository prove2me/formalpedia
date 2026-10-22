-- Prove2me | solution 1 for SelfDualLP.Regularity.theorem_2_iv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:48:00.831075+00:00
-- url     : https://prove2.me/submissions/a64afcd4-34ca-46ca-bc09-97f130d29a3b

import Mathlib
import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix


namespace SelfDualLP.Regularity

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
    -(bBar A b x0 ⬝ᵥ y) + cBar A c y0 s0 ⬝ᵥ x - zBar b c x0 y0 * τ
      = -(x0 ⬝ᵥ s) - (s0 ⬝ᵥ x) - τ - κ := by
  have h1 : (A *ᵥ x0) ⬝ᵥ y = x0 ⬝ᵥ (Aᵀ *ᵥ y) := dot_mulVec_transpose A x0 y
  have h2 : (Aᵀ *ᵥ y0) ⬝ᵥ x = y0 ⬝ᵥ (A *ᵥ x) := by
    rw [dotProduct_comm, ← dot_mulVec_transpose]; rw [dotProduct_comm]
  have h3 : x0 ⬝ᵥ (Aᵀ *ᵥ y) = τ * (x0 ⬝ᵥ c) - x0 ⬝ᵥ s := by
    have : Aᵀ *ᵥ y = τ • c - s := by rw [E2]; abel
    rw [this, dotProduct_sub, dotProduct_smul]; simp
  have h4 : y0 ⬝ᵥ (A *ᵥ x) = τ * (y0 ⬝ᵥ b) := by rw [E1, dotProduct_smul]; simp
  unfold bBar cBar zBar
  rw [sub_dotProduct, sub_dotProduct, sub_dotProduct, h1, h2, h3, h4, E3]
  rw [dotProduct_comm c x0, dotProduct_comm y0 b]
  ring

lemma hlp_obj (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c x0 s0 : Fin n → ℝ) (y0 : Fin m → ℝ)
    (w : HLPPoint m n) (hw : HLPFeasible A b c x0 y0 s0 w) :
    HLPObjective x0 s0 w = w.x ⬝ᵥ w.s + w.τ * w.κ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hw
  have e1 : A *ᵥ w.x = w.τ • b - w.θ • bBar A b x0 := by
    rw [sub_eq_add_neg, ← sub_eq_zero]; rw [← h1]; abel_nf
  have h5 : (A *ᵥ w.x) ⬝ᵥ w.y = w.x ⬝ᵥ (Aᵀ *ᵥ w.y) := dot_mulVec_transpose A w.x w.y
  rw [e1, sub_dotProduct, smul_dotProduct, smul_dotProduct] at h5
  have h6 : w.x ⬝ᵥ w.s = -(w.x ⬝ᵥ (Aᵀ *ᵥ w.y)) + w.τ * (w.x ⬝ᵥ c) - w.θ * (w.x ⬝ᵥ cBar A c y0 s0) := by
    rw [h2, dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul, dotProduct_smul]; simp
  rw [dotProduct_comm (bBar A b x0) w.y, dotProduct_comm (cBar A c y0 s0) w.x] at *
  rw [dotProduct_comm w.x c] at h6
  unfold HLPObjective
  have h7 : w.τ * w.κ = w.τ * (b ⬝ᵥ w.y) - w.τ * (c ⬝ᵥ w.x) + w.τ * zBar b c x0 y0 * w.θ := by
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

theorem t2iv_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    (∃ w : HLPPoint m n,
      IsHLPOptimal A b c x₀ y₀ s₀ w ∧ HLPObjective x₀ s₀ w = 0) ∧
    ∀ w : HLPPoint m n, HLPFeasible A b c x₀ y₀ s₀ w →
      HLPObjective x₀ s₀ w = w.x ⬝ᵥ w.s + w.τ * w.κ := by
  refine ⟨?_, fun w hw => hlp_obj A b c x₀ s₀ y₀ w hw⟩
  obtain ⟨w, hw, hθ⟩ := hlp_exists A b c x₀ s₀ y₀ hx₀ hs₀
  have h0 : HLPObjective x₀ s₀ w = 0 := by simp [HLPObjective, hθ]
  refine ⟨w, ⟨hw, fun v hv => ?_⟩, h0⟩
  rw [h0, hlp_obj A b c x₀ s₀ y₀ v hv]
  obtain ⟨-, -, -, -, hx, hτ, hs, hκ⟩ := hv
  have : 0 ≤ v.x ⬝ᵥ v.s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))
  have := mul_nonneg hτ hκ
  linarith

theorem cor4_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n)
    (hw : IsSelfComplementary A b c w) (hκ : 0 < w.κ) :
    (¬ ∃ x, PrimalFeasible A b c x) ∨
      (¬ ∃ y, DualFeasible A c y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨xh, hxh⟩, ⟨yh, hyh⟩⟩ := hcon
  obtain ⟨hfeas, hopt⟩ := hw
  obtain ⟨v, hv, hvθ⟩ := hlp_exists A b c (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ => one_pos) (fun _ => one_pos)
  have h1 := hopt v hv
  have hv0 : HLPObjective (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) v = 0 := by simp [HLPObjective, hvθ]
  rw [hv0] at h1
  have hobj := hlp_obj A b c (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) w hfeas
  obtain ⟨e1, e2, e3, e4, hx, hτ, hs, -⟩ := hfeas
  have hxs : 0 ≤ w.x ⬝ᵥ w.s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))
  have hτκ : 0 ≤ w.τ * w.κ := mul_nonneg hτ hκ.le
  have hτ0 : w.τ = 0 := by
    have : w.τ * w.κ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  have hθ0 : w.θ = 0 := by
    have hpos : 0 < ((fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (fun _ : Fin n => (1 : ℝ)) + 1) := by
      have : 0 ≤ ((fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (fun _ : Fin n => (1 : ℝ))) :=
        Finset.sum_nonneg (fun j _ => by simp)
      linarith
    have : HLPObjective (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) w = 0 := by linarith
    simp only [HLPObjective] at this
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  simp only [hτ0, hθ0, zero_smul, sub_zero, add_zero, zero_mul, mul_zero] at e1 e2 e3
  -- e1 : A *ᵥ w.x = 0 ; e2 : w.s = -(Aᵀ *ᵥ w.y) ; e3 : w.κ = b ⬝ᵥ w.y - c ⬝ᵥ w.x
  have hAx : ∀ i, A i ⬝ᵥ xh = b i := fun i => by
    have := hxh.1 i
    simpa [LinearOptimization.stdFormLP, LinearOptimization.LinearConstraint.IsSatisfiedAt] using this
  have hxh0 : ∀ j, 0 ≤ xh j := fun j => by
    have := hxh.2 j
    simpa [LinearOptimization.stdFormLP, LinearOptimization.VarSign.IsSatisfiedBy] using this
  have hAxh : A *ᵥ xh = b := funext hAx
  have hyh' : ∀ j, (Aᵀ *ᵥ yh) j ≤ c j := fun j => hyh j
  -- b ⬝ᵥ w.y ≤ 0
  have hby : b ⬝ᵥ w.y ≤ 0 := by
    rw [← hAxh, dot_mulVec_transpose]
    apply Finset.sum_nonpos
    intro j _
    have : (Aᵀ *ᵥ w.y) j = -(w.s j) := by
      have := congrFun e2 j
      simp at this ⊢; linarith
    rw [this]
    nlinarith [hxh0 j, hs j]
  have hcx : 0 ≤ c ⬝ᵥ w.x := by
    have : (A *ᵥ w.x) ⬝ᵥ yh = 0 := by rw [e1]; simp
    rw [dot_mulVec_transpose] at this
    have h2 : w.x ⬝ᵥ (Aᵀ *ᵥ yh) ≤ w.x ⬝ᵥ c :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hyh' j) (hx j))
    rw [dotProduct_comm c]
    linarith
  linarith

end Hlp

end SelfDualLP.Regularity

open SelfDualLP.Regularity


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    (∃ w : HLPPoint m n,
      IsHLPOptimal A b c x₀ y₀ s₀ w ∧ HLPObjective x₀ s₀ w = 0) ∧
    ∀ w : HLPPoint m n, HLPFeasible A b c x₀ y₀ s₀ w →
      HLPObjective x₀ s₀ w = w.x ⬝ᵥ w.s + w.τ * w.κ := by
  exact t2iv_core A b c x₀ y₀ s₀ hx₀ hs₀
