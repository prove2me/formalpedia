-- Prove2me | solution 1 for SteurerHDX.section_2_3_flags
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:27:12.441672+00:00
-- url     : https://prove2.me/submissions/f107abc0-9e6a-4c3b-bb4d-4947563727bc

import Mathlib
import Definitions.Def_SteurerHDX_lambdaTwo
import Theorems.Thm_SteurerHDX_lemma_2_1
import Definitions.Def_SteurerHDX_flagsComplex
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_lambdaTau
import Definitions.Def_SteurerHDX_skeleton1
import Definitions.Def_SteurerHDX_faces
import Definitions.Def_SteurerHDX_link
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsPartite
import Definitions.Def_SteurerHDX_degree

section
set_option autoImplicit false
namespace SteurerHDX.Dev.Flags
open SteurerHDX

lemma vdeg_adj {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] (x : ι) :
    vdeg (G.adjMatrix ℝ) x = (G.degree x : ℝ) := by
  have h := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := x)
  simp only [mul_one] at h
  rw [← h]; simp [vdeg, Matrix.mulVec, dotProduct]

lemma lambdaTwo_le_of_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hpos : ∀ x, 0 < G.degree x) (hcard : 2 ≤ Fintype.card ι) (c0 : ℝ)
    (hK : ∀ f : ι → ℝ, ∑ x, (G.degree x : ℝ) * f x = 0 →
      ∑ x, ∑ y, (G.adjMatrix ℝ) x y * f x * f y ≤ c0 * ∑ x, (G.degree x : ℝ) * f x ^ 2) :
    lambdaTwo (G.adjMatrix ℝ) ≤ c0 := by
  have hsymm : ∀ x y, (G.adjMatrix ℝ) x y = (G.adjMatrix ℝ) y x := by
    intro x y; simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hnn : ∀ x y, 0 ≤ (G.adjMatrix ℝ) x y := by
    intro x y; simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
  have hdeg : ∀ x, 0 < vdeg (G.adjMatrix ℝ) x := by
    intro x; rw [vdeg_adj]; exact_mod_cast hpos x
  obtain ⟨⟨f, hf0, hf1, hfe⟩, -⟩ := (lemma_2_1 (G.adjMatrix ℝ) hcard hsymm hnn hdeg).1
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set S : ℝ := ∑ y, vdeg (G.adjMatrix ℝ) y with hS
  have hSpos : 0 < S := Finset.sum_pos (fun y _ => hdeg y) Finset.univ_nonempty
  set W := G.adjMatrix ℝ with hW
  have hd : ∀ x, vdeg W x = (G.degree x : ℝ) := vdeg_adj G
  have hcol : ∀ y, ∑ x, W x y = (G.degree y : ℝ) := by
    intro y; rw [← hd y]; simp only [vdeg]; exact Finset.sum_congr rfl (fun x _ => hsymm x y)
  have hπ : ∀ x, statDist W x = (G.degree x : ℝ) / S := fun x => by simp [statDist, hd, hS]
  have hsum1 : ∑ x, (G.degree x : ℝ) * f x = 0 := by
    have : innerMu W f (fun _ => 1) = (∑ x, (G.degree x : ℝ) * f x) / S := by
      simp only [innerMu, hπ, Finset.sum_div]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [this] at hf1
    exact (div_eq_zero_iff.mp hf1).resolve_right hSpos.ne'
  set D2 : ℝ := ∑ x, (G.degree x : ℝ) * f x ^ 2 with hD2
  have hD2pos : 0 < D2 := by
    obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hf0
    have hnn2 : ∀ x ∈ Finset.univ, 0 ≤ (G.degree x : ℝ) * f x ^ 2 := fun x _ => by positivity
    have := Finset.single_le_sum hnn2 (Finset.mem_univ x0)
    have h0 : 0 < (G.degree x0 : ℝ) * f x0 ^ 2 := by
      have h1 : (0:ℝ) < G.degree x0 := by exact_mod_cast hpos x0
      have hx0' : f x0 ≠ 0 := hx0
      have h2 : 0 < f x0 ^ 2 := by positivity
      exact mul_pos h1 h2
    linarith
  have hM : innerMu W f f = D2 / S := by
    simp only [innerMu, hπ, hD2, Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  set Q : ℝ := ∑ x, ∑ y, W x y * f x * f y with hQ
  have hE : GibbsCongestion.dirichletForm (walk W) (statDist W) f f = (D2 - Q) / S := by
    have h1 : ∀ x y, statDist W x * walk W x y * (f x - f y) * (f x - f y)
        = (W x y * f x ^ 2 - 2 * (W x y * f x * f y) + W x y * f y ^ 2) / S := by
      intro x y
      have hdx : (G.degree x : ℝ) ≠ 0 := by have := hpos x; positivity
      simp only [walk, Matrix.of_apply, hπ, hd]
      field_simp
      ring
    simp only [GibbsCongestion.dirichletForm, h1]
    simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : ∑ x, ∑ y, W x y * f x ^ 2 = D2 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_mul, ← hd x]; rfl
    have e2 : ∑ x, ∑ y, W x y * f y ^ 2 = D2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_mul, hcol y]
    rw [e1, e2]
    field_simp
    ring
  have hlam : 1 - lambdaTwo W = (D2 - Q) / D2 := by
    rw [hfe, hE, hM]; field_simp
  have hQle := hK f hsum1
  have : lambdaTwo W = Q / D2 := by
    have : (D2 - Q) / D2 = 1 - Q / D2 := by field_simp
    linarith
  rw [this, div_le_iff₀ hD2pos]; linarith

lemma lambdaTwo_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) (hW : ∀ x y, W x y = 0) :
    lambdaTwo W = 0 := by
  classical
  unfold lambdaTwo
  split_ifs with h
  · have h0 : symWalk W = 0 := by ext x y; simp [symWalk, hW]
    have := Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA := h.1) |>.mpr h0
    have key : ∀ j, h.1.eigenvalues₀ j = 0 := by
      intro j
      have := congrFun this ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
      simpa [Matrix.IsHermitian.eigenvalues] using this
    exact key _
  · rfl

theorem lambdaTwo_completeBipartite {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (c : ι → Bool) (hall : ∀ x y, G.Adj x y ↔ c x ≠ c y) :
    lambdaTwo (G.adjMatrix ℝ) ≤ 0 := by
  by_cases hpos : ∀ x, 0 < G.degree x
  · by_cases hcard : 2 ≤ Fintype.card ι
    · apply lambdaTwo_le_of_quad G hpos hcard
      intro f hf
      set u : ι → ℝ := fun x => if c x = true then f x else 0 with hu
      set v : ι → ℝ := fun x => if c x = true then 0 else f x with hv
      set a : ℝ := ∑ x, u x with ha
      set b : ℝ := ∑ x, v x with hb
      set nT : ℝ := ((Finset.univ.filter (fun x => c x = true)).card : ℝ) with hnT
      set nF : ℝ := ((Finset.univ.filter (fun x => c x = false)).card : ℝ) with hnF
      have hdeg : ∀ x, (G.degree x : ℝ) = if c x = true then nF else nT := by
        intro x
        have : G.degree x = (Finset.univ.filter (fun y => c y ≠ c x)).card := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1; ext y; simp [hall, ne_comm]
        rw [this]
        cases hx : c x <;> simp [hnT, hnF]
      have h1 : ∑ x, (G.degree x : ℝ) * f x = nF * a + nT * b := by
        rw [ha, hb, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hdeg]; simp only [hu, hv]; split_ifs <;> simp
      have h2 : ∑ x, ∑ y, (G.adjMatrix ℝ) x y * f x * f y = 2 * (a * b) := by
        have : ∀ x y, (G.adjMatrix ℝ) x y * f x * f y = u x * v y + v x * u y := by
          intro x y; simp only [SimpleGraph.adjMatrix_apply, hall, hu, hv]
          cases c x <;> cases c y <;> simp
        simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [← ha, ← hb]; ring
      have key : ∀ x, 0 < (if c x = true then nF else nT) := by
        intro x; rw [← hdeg]; exact_mod_cast hpos x
      obtain ⟨x0⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
      have hnn : 0 < nT ∧ 0 < nF := by
        have k0 := key x0
        cases hx : c x0
        · rw [hx] at k0
          simp at k0
          have hne : (Finset.univ.filter (fun x => c x = true)).Nonempty := Finset.card_pos.mp (by rw [hnT] at k0; exact_mod_cast k0)
          obtain ⟨y, hy⟩ := hne
          have ky := key y
          simp at hy; rw [hy] at ky; simp at ky
          exact ⟨k0, ky⟩
        · rw [hx] at k0
          simp at k0
          have hne : (Finset.univ.filter (fun x => c x = false)).Nonempty := Finset.card_pos.mp (by rw [hnF] at k0; exact_mod_cast k0)
          obtain ⟨y, hy⟩ := hne
          have ky := key y
          simp at hy; rw [hy] at ky; simp at ky
          exact ⟨ky, k0⟩
      obtain ⟨hnTpos, hnFpos⟩ := hnn
      rw [h2]
      have h3 : nF * a = - (nT * b) := by linarith
      have h4 : nF * (a * b) = - (nT * b ^ 2) := by
        calc nF * (a * b) = (nF * a) * b := by ring
          _ = _ := by rw [h3]; ring
      have h5 : nF * (a * b) ≤ 0 := by rw [h4]; nlinarith [sq_nonneg b]
      have h6 : a * b ≤ 0 := by
        by_contra hh; push Not at hh; nlinarith
      nlinarith
    · unfold lambdaTwo; rw [dif_neg (by tauto)]
  · push Not at hpos
    obtain ⟨x, hx⟩ := hpos
    have hx0 : G.degree x = 0 := by omega
    apply le_of_eq
    apply lambdaTwo_zero
    intro u v
    simp only [SimpleGraph.adjMatrix_apply]
    rw [if_neg]
    intro huv
    have hcu : c u ≠ c v := (hall u v).mp huv
    have : c x = c u ∨ c x = c v := by revert hcu; cases c x <;> cases c u <;> cases c v <;> simp
    rcases this with h | h
    · have : G.Adj x v := (hall x v).mpr (by rw [h]; exact hcu)
      have : v ∈ G.neighborFinset x := by simpa using this
      have := Finset.card_pos.mpr ⟨v, this⟩
      rw [SimpleGraph.card_neighborFinset_eq_degree] at this; omega
    · have : G.Adj x u := (hall x u).mpr (by rw [h]; exact hcu.symm)
      have : u ∈ G.neighborFinset x := by simpa using this
      have := Finset.card_pos.mpr ⟨u, this⟩
      rw [SimpleGraph.card_neighborFinset_eq_degree] at this; omega


lemma ineq_abstract {ι : Type*} [Fintype ι] (F : Finset ι) (hF : 0 < (F.card : ℝ)) (v s : ι → ℝ)
    (α : ℝ) (hα : 0 < α) :
    2 * ∑ z ∈ F, v z * s z ≤ α * (∑ z ∈ F, s z ^ 2 - (∑ z ∈ F, s z) ^ 2 / (F.card : ℝ))
      + (1 / α) * ∑ z ∈ F, v z ^ 2 + 2 * (∑ z ∈ F, v z) * (∑ z ∈ F, s z) / (F.card : ℝ) := by
  set m : ℝ := (F.card : ℝ) with hm
  set B : ℝ := ∑ z ∈ F, v z with hB
  set Sg : ℝ := ∑ z ∈ F, s z with hSg
  have hnn : 0 ≤ ∑ z ∈ F, (α * (s z - Sg / m) - (v z - B / m)) ^ 2 :=
    Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hexp : ∑ z ∈ F, (α * (s z - Sg / m) - (v z - B / m)) ^ 2
      = α ^ 2 * (∑ z ∈ F, s z ^ 2 - 2 * (Sg / m) * Sg + m * (Sg / m) ^ 2)
        - 2 * α * (∑ z ∈ F, v z * s z - (B / m) * Sg - (Sg / m) * B + m * (Sg / m) * (B / m))
        + (∑ z ∈ F, v z ^ 2 - 2 * (B / m) * B + m * (B / m) ^ 2) := by
    have : ∀ z, (α * (s z - Sg / m) - (v z - B / m)) ^ 2
        = α ^ 2 * (s z ^ 2 - 2 * (Sg / m) * s z + (Sg / m) ^ 2)
          - 2 * α * (v z * s z - (B / m) * s z - (Sg / m) * v z + (Sg / m) * (B / m))
          + (v z ^ 2 - 2 * (B / m) * v z + (B / m) ^ 2) := fun z => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, nsmul_eq_mul]
    rw [← hSg, ← hB]
    simp only [hm]; ring
  have hmne : m ≠ 0 := hF.ne'
  have h2 : 0 ≤ α ^ 2 * (∑ z ∈ F, s z ^ 2 - Sg ^ 2 / m) - 2 * α * (∑ z ∈ F, v z * s z - B * Sg / m)
      + (∑ z ∈ F, v z ^ 2 - B ^ 2 / m) := by
    rw [hexp] at hnn
    have e : ∀ x y : ℝ, x / m * y = x * y / m := fun x y => by ring
    field_simp at hnn ⊢
    nlinarith [hnn]
  have h3 : 0 ≤ B ^ 2 / m := by positivity
  have h4 : 2 * α * (∑ z ∈ F, v z * s z) ≤ α ^ 2 * (∑ z ∈ F, s z ^ 2 - Sg ^ 2 / m) + ∑ z ∈ F, v z ^ 2
      + 2 * α * (B * Sg / m) := by nlinarith
  have h5 : (2 * ∑ z ∈ F, v z * s z) = (2 * α * (∑ z ∈ F, v z * s z)) / α := by field_simp
  rw [h5]
  rw [div_le_iff₀ hα]
  have : (α * (∑ z ∈ F, s z ^ 2 - Sg ^ 2 / m) + 1 / α * ∑ z ∈ F, v z ^ 2 + 2 * B * Sg / m) * α
      = α ^ 2 * (∑ z ∈ F, s z ^ 2 - Sg ^ 2 / m) + ∑ z ∈ F, v z ^ 2 + 2 * α * (B * Sg / m) := by
    field_simp
  rw [this]; exact h4

lemma common_one {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (p p' : ι) (h : ∃! z, G.Adj p z ∧ G.Adj p' z) :
    ∑ z, (G.adjMatrix ℝ) z p * (G.adjMatrix ℝ) z p' = 1 := by
  obtain ⟨z0, hz0, hu⟩ := h
  rw [Finset.sum_eq_single z0]
  · simp [SimpleGraph.adjMatrix_apply, hz0.1.symm, hz0.2.symm]
  · intro z _ hz
    have : ¬ (G.Adj p z ∧ G.Adj p' z) := fun hh => hz (hu z hh)
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs with h1 h2
    · exact absurd ⟨h1.symm, h2.symm⟩ this
    all_goals simp
  · simp

lemma common_self {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (p : ι) : ∑ z, (G.adjMatrix ℝ) z p * (G.adjMatrix ℝ) z p = (G.degree p : ℝ) := by
  have h := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := p)
  simp only [mul_one] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]
  split_ifs <;> simp

lemma count_T {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (c : ι → Bool) (hc : ∀ x y, G.Adj x y → c x ≠ c y) (q : ℕ)
    (hone : ∀ x y, c x = true → c y = true → x ≠ y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ z, c z = false → G.degree z = q + 1) (p : ι) (hp : c p = true) :
    (Finset.univ.filter (fun x => c x = true)).card = G.degree p * q + 1 := by
  have hset : (Finset.univ.filter (fun x => c x = true)).erase p
      = (G.neighborFinset p).biUnion (fun z => (G.neighborFinset z).erase p) := by
    ext w
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hwp, hw⟩
      obtain ⟨z, hz, -⟩ := hone p w hp hw (Ne.symm hwp)
      exact ⟨z, hz.1, hwp, hz.2.symm⟩
    · rintro ⟨z, hz, hwp, hwz⟩
      refine ⟨hwp, ?_⟩
      have h1 := hc p z hz
      have h2 := hc z w hwz
      revert h1 h2; rw [hp]; cases c z <;> cases c w <;> simp
  have hcard : ((Finset.univ.filter (fun x => c x = true)).erase p).card = G.degree p * q := by
    rw [hset, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (g := fun _ => q)]
      · simp [SimpleGraph.card_neighborFinset_eq_degree]
      · intro z hz
        have hz' : G.Adj p z := by simpa using hz
        have hcz : c z = false := by
          have := hc p z hz'; rw [hp] at this; cases h : c z <;> simp_all
        rw [Finset.card_erase_of_mem (by simpa using hz'.symm), SimpleGraph.card_neighborFinset_eq_degree,
          hdeg z hcz]; rfl
    · intro z1 hz1 z2 hz2 hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw1 hw2 hz1 hz2
      have h1 := hc p z1 (by simpa using hz1)
      have h2 := hc z1 w hw1.2
      have hw : c w = true := by revert h1 h2; rw [hp]; cases c z1 <;> cases c w <;> simp
      obtain ⟨z, -, hu⟩ := hone p w hp hw (Ne.symm hw1.1)
      exact hne ((hu z1 ⟨by simpa using hz1, hw1.2.symm⟩).trans (hu z2 ⟨by simpa using hz2, hw2.2.symm⟩).symm)
  have := Finset.card_erase_add_one (s := Finset.univ.filter (fun x => c x = true)) (a := p)
    (by simp [hp])
  omega
lemma key_ineq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (c : ι → Bool) (hc : ∀ x y, G.Adj x y → c x ≠ c y) (q : ℕ)
    (hone : ∀ x y, c x = true → c y = true → x ≠ y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ z, c z = false → G.degree z = q + 1)
    (r0 : ℕ) (hr1 : 1 ≤ r0) (hr : ∀ p, c p = true → G.degree p = r0)
    (hT : (Finset.univ.filter (fun x => c x = true)).card = r0 * q + 1)
    (hFT : ((Finset.univ.filter (fun x => c x = false)).card : ℝ) * ((q : ℝ) + 1)
      = ((Finset.univ.filter (fun x => c x = true)).card : ℝ) * r0)
    (hFpos : 0 < (Finset.univ.filter (fun x => c x = false)).card)
    (f : ι → ℝ) (hf : ∑ x, (G.degree x : ℝ) * f x = 0) :
    ∑ x, ∑ y, (G.adjMatrix ℝ) x y * f x * f y
      ≤ (1 / Real.sqrt ((q : ℝ) + 1)) * ∑ x, (G.degree x : ℝ) * f x ^ 2 := by
  set A := G.adjMatrix ℝ with hA
  have hAsymm : ∀ x y, A x y = A y x := by
    intro x y; simp [hA, SimpleGraph.adjMatrix_apply, G.adj_comm]
  set u : ι → ℝ := fun x => if c x = true then f x else 0 with hu
  set v : ι → ℝ := fun x => if c x = true then 0 else f x with hv
  set a : ℝ := ∑ x, u x with ha
  set b : ℝ := ∑ x, v x with hb
  set U : ℝ := ∑ x, u x ^ 2 with hU
  set V : ℝ := ∑ x, v x ^ 2 with hV
  set s : ι → ℝ := fun z => ∑ y, A z y * u y with hs
  set Fs := Finset.univ.filter (fun x => c x = false) with hFs
  set m : ℝ := (Fs.card : ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; exact_mod_cast hFpos
  have hsF : ∀ g : ι → ℝ, (∀ z, c z = true → g z = 0) → ∑ z ∈ Fs, g z = ∑ z, g z := by
    intro g hg
    rw [hFs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    cases h : c z
    · simp
    · simp [hg z h]
  have hvT : ∀ z, c z = true → v z = 0 := fun z h => by simp [hv, h]
  have huF : ∀ z, c z = false → u z = 0 := fun z h => by simp [hu, h]
  have hsT : ∀ z, c z = true → s z = 0 := by
    intro z hz
    simp only [hs]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    by_cases hadj : G.Adj z y
    · have := hc z y hadj
      have hy : c y = false := by rw [hz] at this; cases h : c y <;> simp_all
      rw [huF y hy]; simp
    · simp [hA, SimpleGraph.adjMatrix_apply, hadj]
  -- Q = 2 Σ v s
  have hQ : ∑ x, ∑ y, A x y * f x * f y = 2 * ∑ z, v z * s z := by
    have hpt : ∀ x y, A x y * f x * f y = A x y * u x * v y + A x y * v x * u y := by
      intro x y
      simp only [hA, SimpleGraph.adjMatrix_apply, hu, hv]
      by_cases hadj : G.Adj x y
      · have := hc x y hadj
        cases hx : c x <;> cases hy : c y <;> simp_all
      · simp [hadj]
    simp only [hpt, Finset.sum_add_distrib]
    have e1 : ∑ x, ∑ y, A x y * u x * v y = ∑ z, v z * s z := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hAsymm x y]; ring
    have e2 : ∑ x, ∑ y, A x y * v x * u y = ∑ z, v z * s z := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      ring
    rw [e1, e2]; ring
  -- sums over F
  have hvs : ∑ z ∈ Fs, v z * s z = ∑ z, v z * s z := hsF _ (fun z h => by simp [hvT z h])
  have hv1 : ∑ z ∈ Fs, v z = b := hsF _ hvT
  have hv2 : ∑ z ∈ Fs, v z ^ 2 = V := hsF _ (fun z h => by simp [hvT z h])
  have hs1 : ∑ z ∈ Fs, s z = r0 * a := by
    rw [hsF _ hsT]
    simp only [hs]
    rw [Finset.sum_comm]
    rw [ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.sum_mul]
    have : ∑ x, A x y = (G.degree y : ℝ) := by
      have h := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := y)
      simp only [mul_one] at h
      rw [← h]
      simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one]
      exact Finset.sum_congr rfl (fun x _ => hAsymm x y)
    rw [this]
    by_cases hy : c y = true
    · rw [hr y hy]
    · have : c y = false := by simpa using hy
      rw [huF y this]; simp
  have hs2 : ∑ z ∈ Fs, s z ^ 2 = (r0 - 1) * U + a ^ 2 := by
    rw [hsF _ (fun z h => by simp [hsT z h])]
    have e : ∀ z, s z ^ 2 = ∑ p, ∑ p', u p * u p' * (A z p * A z p') := by
      intro z
      simp only [hs, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun p' _ => ?_))
      ring
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ p, ∑ z, ∑ p', u p * u p' * (A z p * A z p') = ∑ p', ∑ z, u p * u p' * (A z p * A z p') :=
      fun p => Finset.sum_comm
    simp only [e2, ← Finset.mul_sum]
    have e3 : ∀ p p', u p * u p' * ∑ z, A z p * A z p'
        = u p * u p' + (r0 - 1) * (if p = p' then u p ^ 2 else 0) := by
      intro p p'
      by_cases hp : c p = true
      · by_cases hp' : c p' = true
        · by_cases hpp : p = p'
          · subst hpp
            rw [hA, common_self G p, hr p hp]
            simp; ring
          · rw [hA, common_one G p p' (hone p p' hp hp' hpp)]
            simp [hpp]
        · have := huF p' (by simpa using hp')
          simp [this]
          intro hpp; right; rw [hpp]; exact this
      · have := huF p (by simpa using hp)
        simp [this]
    simp only [e3, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e4 : ∑ x, u x * ∑ i, u i = a ^ 2 := by
      rw [← Finset.sum_mul, ha, sq]
    have e5 : ∑ i, ∑ i_1, (if i = i_1 then u i ^ 2 else 0) = U := by
      simp [hU]
    rw [e4, e5]; ring
  have hpt1 : ∀ x, (G.degree x : ℝ) * f x = r0 * u x + ((q : ℝ) + 1) * v x := by
    intro x
    simp only [hu, hv]
    cases hx : c x
    · rw [hdeg x hx]; simp
    · rw [hr x hx]; simp
  have hpt2 : ∀ x, (G.degree x : ℝ) * f x ^ 2 = r0 * u x ^ 2 + ((q : ℝ) + 1) * v x ^ 2 := by
    intro x
    simp only [hu, hv]
    cases hx : c x
    · rw [hdeg x hx]; simp
    · rw [hr x hx]; simp
  have hlin : (r0 : ℝ) * a + ((q : ℝ) + 1) * b = 0 := by
    rw [← hf]; simp only [hpt1, Finset.sum_add_distrib, ← Finset.mul_sum, ha, hb]
  have hD2 : ∑ x, (G.degree x : ℝ) * f x ^ 2 = r0 * U + ((q : ℝ) + 1) * V := by
    simp only [hpt2, Finset.sum_add_distrib, ← Finset.mul_sum, hU, hV]
  rw [hD2, hQ, ← hvs]
  set α : ℝ := 1 / Real.sqrt ((q : ℝ) + 1) with hα
  have hqpos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hαpos : 0 < α := by rw [hα]; positivity
  have hα1 : 1 / α = α * ((q : ℝ) + 1) := by
    rw [hα]
    have hs0 : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr hqpos
    have := Real.sq_sqrt hqpos.le
    field_simp
    nlinarith [this]
  have key := ineq_abstract Fs (by rw [← hm]; exact hmpos) v s α hαpos
  rw [hv1, hv2, hs1, hs2, hα1] at key
  have hmr : m ≤ (r0 : ℝ) ^ 2 := by
    have hT' : ((Finset.univ.filter (fun x => c x = true)).card : ℝ) = r0 * q + 1 := by exact_mod_cast hT
    rw [hT'] at hFT
    have hr1' : (1 : ℝ) ≤ r0 := by exact_mod_cast hr1
    have : m * ((q : ℝ) + 1) ≤ (r0 : ℝ) ^ 2 * ((q : ℝ) + 1) := by nlinarith
    exact le_of_mul_le_mul_right this hqpos
  have t1 : a ^ 2 - (r0 * a) ^ 2 / m ≤ 0 := by
    have : a ^ 2 * m ≤ (r0 * a) ^ 2 := by
      calc a ^ 2 * m ≤ a ^ 2 * (r0 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hmr (sq_nonneg a)
        _ = (r0 * a) ^ 2 := by ring
    have h2 : a ^ 2 ≤ (r0 * a) ^ 2 / m := by rw [le_div_iff₀ hmpos]; exact this
    linarith
  have t3 : 2 * b * (r0 * a) / m ≤ 0 := by
    have : b * (r0 * a) = - (((q : ℝ) + 1) * b ^ 2) := by
      have : (r0 : ℝ) * a = - (((q : ℝ) + 1) * b) := by linarith
      rw [this]; ring
    have h3 : 2 * b * (r0 * a) = -2 * (((q : ℝ) + 1) * b ^ 2) := by linarith
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg _ hmpos.le
    have := mul_nonneg hqpos.le (sq_nonneg b)
    linarith
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hs2' : ((r0 : ℝ) - 1) * U + a ^ 2 - (r0 * a) ^ 2 / m ≤ ((r0 : ℝ) - 1) * U := by linarith
  have : α * (((r0 : ℝ) - 1) * U + a ^ 2 - (r0 * a) ^ 2 / m) ≤ α * (((r0 : ℝ) - 1) * U) :=
    mul_le_mul_of_nonneg_left hs2' hαpos.le
  have h7 := mul_nonneg hαpos.le hU0
  linarith
lemma row_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] (x : ι) :
    ∑ y, (G.adjMatrix ℝ) x y = (G.degree x : ℝ) := by
  have h := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := x)
  simp only [mul_one] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one]

lemma struct_facts {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (c : ι → Bool) (hc : ∀ x y, G.Adj x y → c x ≠ c y) (q : ℕ) (hq : 2 ≤ q)
    (hone : ∀ x y, c x = true → c y = true → x ≠ y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ z, c z = false → G.degree z = q + 1)
    (hpos : ∀ x, 0 < G.degree x) (x0 : ι) :
    ∃ r0 : ℕ, 1 ≤ r0 ∧ (∀ p, c p = true → G.degree p = r0) ∧
      (Finset.univ.filter (fun x => c x = true)).card = r0 * q + 1 ∧
      ((Finset.univ.filter (fun x => c x = false)).card : ℝ) * ((q : ℝ) + 1)
        = ((Finset.univ.filter (fun x => c x = true)).card : ℝ) * r0 ∧
      0 < (Finset.univ.filter (fun x => c x = false)).card := by
  obtain ⟨p0, hp0⟩ : ∃ p0, c p0 = true := by
    cases hx : c x0
    · have h0 := hpos x0
      have hn : 0 < (G.neighborFinset x0).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact h0
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hn
      have hadj : G.Adj x0 y := by simpa using hy
      have := hc x0 y hadj
      refine ⟨y, ?_⟩
      rw [hx] at this; cases h : c y <;> simp_all
    · exact ⟨x0, hx⟩
  have hqpos : 0 < q := by omega
  have hr : ∀ p, c p = true → G.degree p = G.degree p0 := by
    intro p hp
    have h1 := count_T G c hc q hone hdeg p hp
    have h2 := count_T G c hc q hone hdeg p0 hp0
    have : G.degree p * q = G.degree p0 * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hqpos this
  have hFne : 0 < (Finset.univ.filter (fun x => c x = false)).card := by
    have h0 := hpos p0
    have hn : 0 < (G.neighborFinset p0).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact h0
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hn
    have hadj : G.Adj p0 y := by simpa using hy
    have := hc p0 y hadj
    rw [hp0] at this
    apply Finset.card_pos.mpr
    refine ⟨y, ?_⟩
    simp; cases h : c y <;> simp_all
  refine ⟨G.degree p0, hpos p0, hr, count_T G c hc q hone hdeg p0 hp0, ?_, hFne⟩
  -- double counting
  have hpt : ∀ x y, (if c x = false then (G.adjMatrix ℝ) x y else 0)
      = (if c y = true then (G.adjMatrix ℝ) y x else 0) := by
    intro x y
    by_cases hadj : G.Adj x y
    · have := hc x y hadj
      simp only [SimpleGraph.adjMatrix_apply, hadj, (G.adj_comm x y).mp hadj, if_true]
      cases hx : c x <;> cases hy : c y <;> simp_all
    · have h2 : ¬ G.Adj y x := fun h => hadj ((G.adj_comm x y).mpr h)
      simp [SimpleGraph.adjMatrix_apply, hadj, h2]
  have hL : ∑ x, ∑ y, (if c x = false then (G.adjMatrix ℝ) x y else 0)
      = ((Finset.univ.filter (fun x => c x = false)).card : ℝ) * ((q : ℝ) + 1) := by
    have : ∀ x, ∑ y, (if c x = false then (G.adjMatrix ℝ) x y else 0)
        = if c x = false then ((q : ℝ) + 1) else 0 := by
      intro x
      split_ifs with h
      · rw [row_sum, hdeg x h]; push_cast; ring
      · simp
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hR : ∑ x, ∑ y, (if c y = true then (G.adjMatrix ℝ) y x else 0)
      = ((Finset.univ.filter (fun x => c x = true)).card : ℝ) * (G.degree p0 : ℝ) := by
    rw [Finset.sum_comm]
    have : ∀ y, ∑ x, (if c y = true then (G.adjMatrix ℝ) y x else 0)
        = if c y = true then (G.degree p0 : ℝ) else 0 := by
      intro y
      split_ifs with h
      · rw [row_sum, hr y h]
      · simp
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← hL, ← hR]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpt x y))

/-- Spectral lemma A: a bipartite graph in which any two distinct vertices of the first colour class
have exactly one common neighbour, all vertices of the second colour class have degree q+1 (q ≥ 2)
has second eigenvalue of the simple random walk at most 1/√(q+1) ≤ 2/(√q-1). -/
theorem lambdaTwo_incidence {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (c : ι → Bool) (hc : ∀ x y, G.Adj x y → c x ≠ c y) (q : ℕ) (hq : 2 ≤ q)
    (hone : ∀ x y, c x = true → c y = true → x ≠ y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ z, c z = false → G.degree z = q + 1)
    (hpos : ∀ x, 0 < G.degree x) :
    lambdaTwo (G.adjMatrix ℝ) ≤ 2 / (Real.sqrt q - 1) := by
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq1 : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hbound : 1 / Real.sqrt ((q : ℝ) + 1) ≤ 2 / (Real.sqrt q - 1) := by
    have h1 : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have h2 : Real.sqrt q ≤ Real.sqrt ((q : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    rw [div_le_div_iff₀ h1 (by linarith)]
    linarith
  by_cases hcard : 2 ≤ Fintype.card ι
  · obtain ⟨x0⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨r0, hr1, hr, hT, hFT, hFpos⟩ := struct_facts G c hc q hq hone hdeg hpos x0
    refine le_trans (lambdaTwo_le_of_quad G hpos hcard (1 / Real.sqrt ((q : ℝ) + 1)) ?_) hbound
    intro f hf
    exact key_ineq G c hc q hone hdeg r0 hr1 hr hT hFT hFpos f hf
  · have : lambdaTwo (G.adjMatrix ℝ) = 0 := by
      unfold lambdaTwo; rw [dif_neg (fun h => hcard h.2)]
    rw [this]
    have : 0 < Real.sqrt q - 1 := by linarith
    positivity

end SteurerHDX.Dev.Flags
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SteurerHDX.Dev.Flags
open SteurerHDX


section Count
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] {N : ℕ}

noncomputable instance instFiniteSub : Finite (Submodule F (Fin N → F)) :=
  Finite.of_injective (fun W : Submodule F (Fin N → F) => (W : Set (Fin N → F))) SetLike.coe_injective

theorem card_mem (M : Submodule F (Fin N → F)) :
    (Finset.univ.filter (fun v : Fin N → F => v ∈ M)).card = Fintype.card F ^ Module.finrank F M := by
  classical
  rw [← Fintype.card_subtype]
  have := Module.card_eq_pow_finrank (K := F) (V := M)
  rw [← this]

theorem card_middle (C E : Submodule F (Fin N → F)) (hCE : C ≤ E)
    (hd : Module.finrank F E = Module.finrank F C + 2) :
    Set.ncard {M : Submodule F (Fin N → F) |
      C ≤ M ∧ M ≤ E ∧ Module.finrank F M = Module.finrank F C + 1} = Fintype.card F + 1 := by
  classical
  have : Fintype (Submodule F (Fin N → F)) := Fintype.ofFinite _
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set c := Module.finrank F C with hc
  let T : Finset (Submodule F (Fin N → F)) :=
    Finset.univ.filter (fun M => C ≤ M ∧ M ≤ E ∧ Module.finrank F M = c + 1)
  have hT : {M : Submodule F (Fin N → F) |
      C ≤ M ∧ M ≤ E ∧ Module.finrank F M = c + 1} = (T : Set _) := by
    ext M; simp [T]
  rw [hT, Set.ncard_coe_finset]
  let f : (Fin N → F) → Submodule F (Fin N → F) := fun v => C ⊔ Submodule.span F ({v} : Set (Fin N → F))
  have hf : ∀ v, f v = C ⊔ Submodule.span F ({v} : Set (Fin N → F)) := fun v => rfl
  let EC : Finset (Fin N → F) := Finset.univ.filter (fun v => v ∈ E ∧ v ∉ C)
  have hCard : ∀ (A B : Submodule F (Fin N → F)), A ≤ B →
      (Finset.univ.filter (fun v : Fin N → F => v ∈ B ∧ v ∉ A)).card =
        q ^ Module.finrank F B - q ^ Module.finrank F A := by
    intro A B hAB
    have : (Finset.univ.filter (fun v : Fin N → F => v ∈ B ∧ v ∉ A)) =
        (Finset.univ.filter (fun v : Fin N → F => v ∈ B)) \ (Finset.univ.filter (fun v : Fin N → F => v ∈ A)) := by
      ext v; simp
    rw [this, Finset.card_sdiff_of_subset, card_mem, card_mem]
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hAB hv
  have h1 : EC.card = q ^ (c + 2) - q ^ c := by
    have := hCard C E hCE
    rw [hd] at this
    exact this
  have hmap : ∀ v ∈ EC, (f v) ∈ T := by
    intro v hv
    simp only [EC, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have hle : f v ≤ E :=
      sup_le hCE ((Submodule.span_singleton_le_iff_mem _ _).2 hv.1)
    have hlt : C < f v := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hv.2
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    refine ⟨le_sup_left, hle, ?_⟩
    have h1 : c < Module.finrank F (f v) := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : Module.finrank F (f v) ≤ c + 1 := by
      have := Submodule.finrank_add_le_finrank_add_finrank C (Submodule.span F ({v} : Set (Fin N → F)))
      have h3 : Module.finrank F (Submodule.span F ({v} : Set (Fin N → F))) ≤ 1 := (by have := finrank_span_finset_le_card (R := F) ({v} : Finset (Fin N → F)); rw [Finset.coe_singleton, Finset.card_singleton] at this; exact this)
      have h4 : Module.finrank F (↥(f v)) ≤ _ := Submodule.finrank_add_le_finrank_add_finrank C (Submodule.span F ({v} : Set (Fin N → F)))
      omega
    omega
  have hfib := Finset.card_eq_sum_card_fiberwise hmap
  have hfib2 : ∀ M ∈ T, (EC.filter (fun v => f v = M)).card = q ^ (c + 1) - q ^ c := by
    intro M hM
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    obtain ⟨hCM, hME, hMd⟩ := hM
    have := hCard C M hCM
    rw [hMd] at this
    rw [← this]
    congr 1
    ext v
    simp only [EC, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hvC⟩, hv⟩
      refine ⟨?_, hvC⟩
      rw [← hv]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    · rintro ⟨hvM, hvC⟩
      refine ⟨⟨hME hvM, hvC⟩, ?_⟩
      have hle : f v ≤ M :=
        sup_le hCM ((Submodule.span_singleton_le_iff_mem _ _).2 hvM)
      have hlt : C < f v := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hvC
        rw [h]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
      have h1 : c < Module.finrank F (f v) := Submodule.finrank_lt_finrank_of_lt hlt
      exact Submodule.eq_of_le_of_finrank_eq hle (by
        have h5 := Submodule.finrank_mono hle
        omega)
  rw [Finset.sum_congr rfl hfib2, Finset.sum_const, smul_eq_mul, h1] at hfib
  have hpos : 0 < q ^ c := pow_pos (by omega) c
  have e1 : q ^ (c + 2) = q ^ c * (q * q) := by ring
  have e2 : q ^ (c + 1) = q ^ c * q := by ring
  rw [e1, e2] at hfib
  have hle1 : q ^ c ≤ q ^ c * q := Nat.le_mul_of_pos_right _ (by omega)
  have hle2 : q ^ c ≤ q ^ c * (q * q) := Nat.le_mul_of_pos_right _ (by nlinarith)
  zify [hle1, hle2] at hfib
  have : (q:ℤ) ^ c * (((q:ℤ) - 1) * (q + 1)) = (q:ℤ) ^ c * (((q:ℤ) - 1) * T.card) := by
    nlinarith [hfib]
  have hz : (q:ℤ) ^ c ≠ 0 := by positivity
  have h3 := mul_left_cancel₀ hz this
  have h4 : ((q:ℤ) - 1) ≠ 0 := by omega
  have := mul_left_cancel₀ h4 h3
  omega

end Count

section Transport
variable {F : Type*} [Field F] [Fintype F] {N : ℕ}

def Cmp (W W' : Submodule F (Fin N → F)) : Prop := W ≠ W' ∧ (W ≤ W' ∨ W' ≤ W)

theorem dim_ne_of_cmp {W W' : Submodule F (Fin N → F)} (h : Cmp W W') :
    Module.finrank F W ≠ Module.finrank F W' := by
  intro hd
  apply h.1
  rcases h.2 with h2 | h2
  · exact Submodule.eq_of_le_of_finrank_eq h2 hd
  · exact (Submodule.eq_of_le_of_finrank_eq h2 hd.symm).symm

theorem incidence_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (w : ι → Submodule F (Fin N → F)) (hinj : Function.Injective w)
    (Ok : Submodule F (Fin N → F) → Prop)
    (hsurj : ∀ W, Ok W → ∃ s, w s = W) (hOk : ∀ s, Ok (w s))
    (hadj : ∀ s t, G.Adj s t ↔ Cmp (w s) (w t))
    (d1 d2 : ℕ) (hd : d1 ≠ d2)
    (hdim : ∀ W, Ok W → Module.finrank F W = d1 ∨ Module.finrank F W = d2)
    (hone : ∀ W1 W2, Ok W1 → Ok W2 → Module.finrank F W1 = d1 → Module.finrank F W2 = d1 →
      W1 ≠ W2 → ∃! W', Ok W' ∧ Cmp W1 W' ∧ Cmp W2 W')
    (hdeg : ∀ W, Ok W → Module.finrank F W = d2 →
      Set.ncard {W' | Ok W' ∧ Cmp W W'} = Fintype.card F + 1)
    (hpos : ∀ W, Ok W → ∃ W', Ok W' ∧ Cmp W W') :
    lambdaTwo (G.adjMatrix ℝ) ≤ 2 / (Real.sqrt (Fintype.card F) - 1) := by
  classical
  refine lambdaTwo_incidence G (fun s => decide (Module.finrank F (w s) = d1)) ?_
    (Fintype.card F) Fintype.one_lt_card ?_ ?_ ?_
  · intro x y hxy
    have h1 := dim_ne_of_cmp ((hadj x y).1 hxy)
    rcases hdim _ (hOk x) with h | h <;> rcases hdim _ (hOk y) with h' | h' <;>
      simp_all <;> omega
  · intro x y hx hy hxy
    simp only [decide_eq_true_eq] at hx hy
    have hne : w x ≠ w y := fun h => hxy (hinj h)
    obtain ⟨W', ⟨hW'ok, hc1, hc2⟩, huniq⟩ := hone _ _ (hOk x) (hOk y) hx hy hne
    obtain ⟨s, hs⟩ := hsurj W' hW'ok
    refine ⟨s, ⟨(hadj _ _).2 (hs ▸ hc1), (hadj _ _).2 (hs ▸ hc2)⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    apply hinj
    rw [hs]
    exact huniq _ ⟨hOk z, (hadj _ _).1 hz1, (hadj _ _).1 hz2⟩
  · intro z hz
    have hz' : Module.finrank F (w z) ≠ d1 := by simpa using hz
    have hz2 : Module.finrank F (w z) = d2 := by
      rcases hdim _ (hOk z) with h | h
      · exact absurd h hz'
      · exact h
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset]
    have e : ((G.neighborFinset z : Finset ι) : Set ι) = {s | G.Adj z s} := by
      ext s; simp
    rw [e, ← Set.ncard_image_of_injective _ hinj]
    rw [← hdeg _ (hOk z) hz2]
    congr 1
    ext W'
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hOk s, (hadj _ _).1 hs⟩
    · rintro ⟨hok, hc⟩
      obtain ⟨s, hs⟩ := hsurj W' hok
      exact ⟨s, (hadj _ _).2 (hs ▸ hc), hs⟩
  · intro x
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨W', hok, hc⟩ := hpos _ (hOk x)
    obtain ⟨s, hs⟩ := hsurj W' hok
    exact ⟨s, (hadj _ _).2 (hs ▸ hc)⟩

theorem bip_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (w : ι → Submodule F (Fin N → F))
    (Ok : Submodule F (Fin N → F) → Prop)
    (hOk : ∀ s, Ok (w s))
    (hadj : ∀ s t, G.Adj s t ↔ Cmp (w s) (w t))
    (d1 : ℕ)
    (hall : ∀ W W', Ok W → Ok W' →
      (Cmp W W' ↔ ¬ (Module.finrank F W = d1 ↔ Module.finrank F W' = d1))) :
    lambdaTwo (G.adjMatrix ℝ) ≤ 0 := by
  classical
  refine lambdaTwo_completeBipartite G (fun s => decide (Module.finrank F (w s) = d1)) ?_
  intro x y
  rw [hadj, hall _ _ (hOk x) (hOk y)]
  simp [decide_eq_decide]

end Transport

section Link
variable {F : Type*} [Field F] [Fintype F] {N : ℕ} [DecidableEq (Submodule F (Fin N → F))]

def IsFl (lo m : ℕ) (s : Finset (Submodule F (Fin N → F))) : Prop :=
  (∀ W ∈ s, lo ≤ Module.finrank F W ∧ Module.finrank F W ≤ lo + m) ∧
  (∀ W ∈ s, ∀ W' ∈ s, W ≤ W' ∨ W' ≤ W)

def OkV (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (W : Submodule F (Fin N → F)) : Prop :=
  W ∉ τ ∧ IsFl lo m (insert W τ)

theorem mem_link_single (lo m : ℕ) (X : Finset (Finset (Submodule F (Fin N → F))))
    (hX : ∀ s, s ∈ X ↔ IsFl lo m s) (τ : Finset (Submodule F (Fin N → F)))
    (W : Submodule F (Fin N → F)) :
    ({W} : Finset _) ∈ link X τ ↔ OkV lo m τ W := by
  unfold link OkV
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨σ, ⟨hσ, hτσ⟩, he⟩
    have hW : W ∈ σ \ τ := by rw [he]; simp
    rw [Finset.mem_sdiff] at hW
    have : insert W τ = σ := by
      ext x
      simp only [Finset.mem_insert]
      constructor
      · rintro (rfl | hx)
        · exact hW.1
        · exact hτσ hx
      · intro hx
        by_cases hxτ : x ∈ τ
        · exact Or.inr hxτ
        · left
          have : x ∈ σ \ τ := Finset.mem_sdiff.2 ⟨hx, hxτ⟩
          rw [he] at this
          simpa using this
    refine ⟨hW.2, ?_⟩
    rw [this]; exact (hX σ).1 hσ
  · rintro ⟨hW, hfl⟩
    refine ⟨insert W τ, ⟨(hX _).2 hfl, Finset.subset_insert _ _⟩, ?_⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hxτ⟩
      · exact hx
      · exact absurd hx hxτ
    · rintro rfl
      exact ⟨Or.inl rfl, hW⟩

theorem mem_link_pair (lo m : ℕ) (X : Finset (Finset (Submodule F (Fin N → F))))
    (hX : ∀ s, s ∈ X ↔ IsFl lo m s) (τ : Finset (Submodule F (Fin N → F)))
    (W W' : Submodule F (Fin N → F)) :
    ({W} ∪ {W'} : Finset _) ∈ link X τ ↔
      (W ∉ τ ∧ W' ∉ τ ∧ IsFl lo m (insert W (insert W' τ))) := by
  unfold link
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨σ, ⟨hσ, hτσ⟩, he⟩
    have hW : W ∈ σ \ τ := by rw [he]; simp
    have hW' : W' ∈ σ \ τ := by rw [he]; simp
    rw [Finset.mem_sdiff] at hW hW'
    have : insert W (insert W' τ) = σ := by
      ext x
      simp only [Finset.mem_insert]
      constructor
      · rintro (rfl | rfl | hx)
        · exact hW.1
        · exact hW'.1
        · exact hτσ hx
      · intro hx
        by_cases hxτ : x ∈ τ
        · exact Or.inr (Or.inr hxτ)
        · have : x ∈ σ \ τ := Finset.mem_sdiff.2 ⟨hx, hxτ⟩
          rw [he] at this
          have := by simpa using this
          tauto
    refine ⟨hW.2, hW'.2, ?_⟩
    rw [this]; exact (hX σ).1 hσ
  · rintro ⟨hW, hW', hfl⟩
    refine ⟨insert W (insert W' τ), ⟨(hX _).2 hfl, ?_⟩, ?_⟩
    · intro x hx
      simp [hx]
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hx | hx | hx, hxτ⟩
        · exact Or.inl hx
        · exact Or.inr hx
        · exact absurd hx hxτ
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hW⟩
        · exact ⟨Or.inr (Or.inl rfl), hW'⟩


theorem isFl_pair_iff (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (hτ : IsFl lo m τ)
    (W W' : Submodule F (Fin N → F)) (hW : OkV lo m τ W) (hW' : OkV lo m τ W') :
    IsFl lo m (insert W (insert W' τ)) ↔ (W ≤ W' ∨ W' ≤ W) := by
  constructor
  · intro h
    exact h.2 W (by simp) W' (by simp)
  · intro hc
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact hW.2.1 _ (by simp)
      · exact hW'.2.1 _ (by simp)
      · exact hτ.1 _ hx
    · intro x hx y hy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | rfl | hx <;> rcases hy with rfl | rfl | hy
      · exact Or.inl le_rfl
      · exact hc
      · exact hW.2.2 _ (by simp) _ (by simp [hy])
      · exact hc.symm
      · exact Or.inl le_rfl
      · exact hW'.2.2 _ (by simp) _ (by simp [hy])
      · exact (hW.2.2 _ (by simp) _ (by simp [hx])).symm
      · exact (hW'.2.2 _ (by simp) _ (by simp [hx])).symm
      · exact hτ.2 _ hx _ hy

theorem link_data (lo m : ℕ) (X : Finset (Finset (Submodule F (Fin N → F))))
    (hX : ∀ s, s ∈ X ↔ IsFl lo m s) (τ : Finset (Submodule F (Fin N → F))) (hτ : τ ∈ X) :
    ∃ w : faces (link X τ) 1 → Submodule F (Fin N → F), Function.Injective w ∧
      (∀ W, OkV lo m τ W → ∃ s, w s = W) ∧ (∀ s, OkV lo m τ (w s)) ∧
      ∀ s t, (skeleton1 (link X τ)).Adj s t ↔ Cmp (w s) (w t) := by
  have hs1 : ∀ s : faces (link X τ) 1, ∃ a, s.1 = {a} :=
    fun s => Finset.card_eq_one.1 (Finset.mem_filter.1 s.2).2
  choose w hw using hs1
  have hOk : ∀ s, OkV lo m τ (w s) := fun s =>
    (mem_link_single lo m X hX τ (w s)).1 (by rw [← hw s]; exact (Finset.mem_filter.1 s.2).1)
  have hinj : Function.Injective w := by
    intro s t h
    apply Subtype.ext
    rw [hw s, hw t, h]
  refine ⟨w, hinj, ?_, hOk, ?_⟩
  · intro W hok
    refine ⟨⟨{W}, Finset.mem_filter.2 ⟨(mem_link_single lo m X hX τ W).2 hok, Finset.card_singleton W⟩⟩, ?_⟩
    have := hw ⟨{W}, Finset.mem_filter.2 ⟨(mem_link_single lo m X hX τ W).2 hok, Finset.card_singleton W⟩⟩
    simpa using this.symm
  · intro s t
    show s ≠ t ∧ s.1 ∪ t.1 ∈ link X τ ↔ _
    rw [hw s, hw t, mem_link_pair lo m X hX]
    have hτfl : IsFl lo m τ := (hX τ).1 hτ
    constructor
    · rintro ⟨hne, h1, h2, h3⟩
      refine ⟨fun h => hne (hinj h), (isFl_pair_iff lo m τ hτfl _ _ (hOk s) (hOk t)).1 h3⟩
    · rintro ⟨hne, hc⟩
      refine ⟨fun h => hne (by rw [h]), (hOk s).1, (hOk t).1, ?_⟩
      exact (isFl_pair_iff lo m τ hτfl _ _ (hOk s) (hOk t)).2 hc

end Link

section Geom
variable {F : Type*} [Field F] [Fintype F] {N : ℕ} [DecidableEq (Submodule F (Fin N → F))]
local notation "dm" => Module.finrank F

theorem finrank_cover {C : Submodule F (Fin N → F)} {v : Fin N → F} (hv : v ∉ C) :
    dm (↥(C ⊔ Submodule.span F ({v} : Set (Fin N → F)) : Submodule F (Fin N → F))) = dm C + 1 := by
  have hlt : C < C ⊔ Submodule.span F ({v} : Set (Fin N → F)) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hv
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 : Module.finrank F (Submodule.span F ({v} : Set (Fin N → F))) ≤ 1 := by
    have := finrank_span_finset_le_card (R := F) ({v} : Finset (Fin N → F))
    rw [Finset.coe_singleton, Finset.card_singleton] at this
    exact this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank C (Submodule.span F ({v} : Set (Fin N → F)))
  omega

theorem exists_cover {C E : Submodule F (Fin N → F)} (hCE : C ≤ E) (hlt : dm C < dm E) :
    ∃ M, C ≤ M ∧ M ≤ E ∧ dm M = dm C + 1 := by
  have hne : C < E := lt_of_le_of_ne hCE (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)
  obtain ⟨v, hvE, hvC⟩ := SetLike.exists_of_lt hne
  refine ⟨C ⊔ Submodule.span F ({v} : Set (Fin N → F)), le_sup_left,
    sup_le hCE ((Submodule.span_singleton_le_iff_mem _ _).2 hvE), finrank_cover hvC⟩

theorem exists_sub (E : Submodule F (Fin N → F)) (e : ℕ) (he : e ≤ dm E) :
    ∃ M, M ≤ E ∧ dm M = e := by
  induction e with
  | zero => exact ⟨⊥, bot_le, by simp⟩
  | succ e ih =>
    obtain ⟨M, hME, hM⟩ := ih (by omega)
    obtain ⟨M', -, h2, h3⟩ := exists_cover hME (by omega)
    exact ⟨M', h2, by omega⟩

theorem le_of_cmp_dim {A B : Submodule F (Fin N → F)} (h : A ≤ B ∨ B ≤ A) (hd : dm A ≤ dm B) :
    A ≤ B := by
  rcases h with h | h
  · exact h
  · exact (Submodule.eq_of_le_of_finrank_eq h (le_antisymm (Submodule.finrank_mono h) hd)).ge

theorem eq_of_cmp_dim_eq {A B : Submodule F (Fin N → F)} (h : A ≤ B ∨ B ≤ A) (hd : dm A = dm B) :
    A = B := by
  rcases h with h | h
  · exact Submodule.eq_of_le_of_finrank_eq h hd
  · exact (Submodule.eq_of_le_of_finrank_eq h hd.symm).symm

theorem tau_dims (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (hτ : IsFl lo m τ)
    (hcard : τ.card + 2 = m + 1) :
    ∃ sa sb, sa < sb ∧ lo ≤ sa ∧ sb ≤ lo + m ∧ (∀ T ∈ τ, dm T ≠ sa ∧ dm T ≠ sb) ∧
      (∀ d, lo ≤ d → d ≤ lo + m → d ≠ sa → d ≠ sb → ∃ T ∈ τ, dm T = d) := by
  classical
  let D : Finset ℕ := τ.image (fun T : Submodule F (Fin N → F) => dm T)
  have hinj : Set.InjOn (fun T : Submodule F (Fin N → F) => dm T) (τ : Set _) :=
    fun T hT T' hT' h => eq_of_cmp_dim_eq (hτ.2 T hT T' hT') h
  have hDcard : D.card = τ.card := Finset.card_image_of_injOn hinj
  have hDsub : D ⊆ Finset.Icc lo (lo + m) := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hd
    exact Finset.mem_Icc.2 (hτ.1 T hT)
  have hP : (Finset.Icc lo (lo + m) \ D).card = 2 := by
    rw [Finset.card_sdiff_of_subset hDsub]
    simp only [Nat.card_Icc]
    omega
  obtain ⟨x, y, hxy, hP2⟩ := Finset.card_eq_two.1 hP
  have key : ∀ d, d ∈ Finset.Icc lo (lo + m) → (d ∉ D ↔ d = x ∨ d = y) := by
    intro d hd
    have := Finset.ext_iff.1 hP2 d
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have hx : x ∈ Finset.Icc lo (lo + m) := by
    have := (Finset.ext_iff.1 hP2 x).2 (by simp)
    exact (Finset.mem_sdiff.1 this).1
  have hy : y ∈ Finset.Icc lo (lo + m) := by
    have := (Finset.ext_iff.1 hP2 y).2 (by simp)
    exact (Finset.mem_sdiff.1 this).1
  have main : ∀ a b, a < b → a ∈ Finset.Icc lo (lo + m) → b ∈ Finset.Icc lo (lo + m) →
      (∀ d, d ∈ Finset.Icc lo (lo + m) → (d ∉ D ↔ d = a ∨ d = b)) →
      ∃ sa sb, sa < sb ∧ lo ≤ sa ∧ sb ≤ lo + m ∧ (∀ T ∈ τ, dm T ≠ sa ∧ dm T ≠ sb) ∧
      (∀ d, lo ≤ d → d ≤ lo + m → d ≠ sa → d ≠ sb → ∃ T ∈ τ, dm T = d) := by
    intro a b hab ha hb hk
    refine ⟨a, b, hab, (Finset.mem_Icc.1 ha).1, (Finset.mem_Icc.1 hb).2, ?_, ?_⟩
    · intro T hT
      have hTD : dm T ∈ D := Finset.mem_image_of_mem _ hT
      constructor
      · intro h
        have := (hk a ha).2 (Or.inl rfl)
        rw [h] at hTD; exact this hTD
      · intro h
        have := (hk b hb).2 (Or.inr rfl)
        rw [h] at hTD; exact this hTD
    · intro d hd1 hd2 hda hdb
      have hdI : d ∈ Finset.Icc lo (lo + m) := Finset.mem_Icc.2 ⟨hd1, hd2⟩
      have : d ∈ D := by
        by_contra hnot
        rcases (hk d hdI).1 hnot with h | h
        · exact hda h
        · exact hdb h
      obtain ⟨T, hT, hTd⟩ := Finset.mem_image.1 this
      exact ⟨T, hT, hTd⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact main x y h hx hy (fun d hd => by rw [key d hd])
  · exact main y x h hy hx (fun d hd => by rw [key d hd]; tauto)

theorem ok_dim (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa sb : ℕ)
    (hT : ∀ T ∈ τ, dm T ≠ sa ∧ dm T ≠ sb)
    (hex : ∀ d, lo ≤ d → d ≤ lo + m → d ≠ sa → d ≠ sb → ∃ T ∈ τ, dm T = d)
    {W : Submodule F (Fin N → F)} (hW : OkV lo m τ W) : dm W = sa ∨ dm W = sb := by
  by_contra hne
  simp only [not_or] at hne
  have hr := hW.2.1 W (Finset.mem_insert_self _ _)
  obtain ⟨T, hTτ, hTd⟩ := hex (dm W) hr.1 hr.2 hne.1 hne.2
  have hc := hW.2.2 W (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hTτ)
  have := eq_of_cmp_dim_eq hc hTd.symm
  exact hW.1 (this ▸ hTτ)

theorem le_of_ok_lt (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F)))
    {W T : Submodule F (Fin N → F)} (hW : OkV lo m τ W) (hT : T ∈ τ) (h : dm T < dm W) :
    T ≤ W :=
  le_of_cmp_dim ((hW.2.2 W (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hT)).symm) h.le

theorem ge_of_ok_lt (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F)))
    {W T : Submodule F (Fin N → F)} (hW : OkV lo m τ W) (hT : T ∈ τ) (h : dm W < dm T) :
    W ≤ T :=
  le_of_cmp_dim (hW.2.2 W (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hT)) h.le


structure TauData (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa sb : ℕ) : Prop where
  hlt : sa < sb
  hsa : lo ≤ sa
  hsb : sb ≤ lo + m
  hT : ∀ T ∈ τ, dm T ≠ sa ∧ dm T ≠ sb
  hex : ∀ d, lo ≤ d → d ≤ lo + m → d ≠ sa → d ≠ sb → ∃ T ∈ τ, dm T = d

theorem case_one (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa sb : ℕ)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa sb) (h : sa + 1 < sb) :
    ∀ W W' : Submodule F (Fin N → F), OkV lo m τ W → OkV lo m τ W' →
      (Cmp W W' ↔ ¬ (dm W = sa ↔ dm W' = sa)) := by
  have claim : ∀ W W' : Submodule F (Fin N → F), OkV lo m τ W → OkV lo m τ W' →
      dm W = sa → dm W' = sb → W ≤ W' := by
    intro W W' hW hW' hd hd'
    obtain ⟨T1, hT1, hT1d⟩ := D.hex (sa + 1) (by have := D.hsa; omega) (by have := D.hsb; omega)
      (by omega) (by omega)
    obtain ⟨T2, hT2, hT2d⟩ := D.hex (sb - 1) (by have := D.hsa; omega) (by have := D.hsb; omega)
      (by omega) (by omega)
    have h1 : W ≤ T1 := ge_of_ok_lt lo m τ hW hT1 (by omega)
    have h2 : T1 ≤ T2 := le_of_cmp_dim (hτ.2 T1 hT1 T2 hT2) (by omega)
    have h3 : T2 ≤ W' := le_of_ok_lt lo m τ hW' hT2 (by omega)
    exact h1.trans (h2.trans h3)
  intro W W' hW hW'
  have hne : sa ≠ sb := by omega
  rcases ok_dim lo m τ sa sb D.hT D.hex hW with h1 | h1 <;>
    rcases ok_dim lo m τ sa sb D.hT D.hex hW' with h2 | h2
  · constructor
    · intro hc; exact absurd (h1.trans h2.symm) (dim_ne_of_cmp hc)
    · intro hc; exact absurd ⟨fun _ => h2, fun _ => h1⟩ hc
  · have hle := claim W W' hW hW' h1 h2
    constructor
    · intro _ hh
      have := hh.1 h1
      omega
    · intro _
      refine ⟨fun he => ?_, Or.inl hle⟩
      rw [he] at h1; omega
  · have hle := claim W' W hW' hW h2 h1
    constructor
    · intro _ hh
      have := hh.2 h2
      omega
    · intro _
      refine ⟨fun he => ?_, Or.inr hle⟩
      rw [he] at h1; omega
  · constructor
    · intro hc; exact absurd (h1.trans h2.symm) (dim_ne_of_cmp hc)
    · intro hc
      exfalso
      apply hc
      constructor <;> intro hh <;> omega

noncomputable def Lof (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ) : Submodule F (Fin N → F) :=
  (τ.filter (fun T : Submodule F (Fin N → F) => dm T < sa)).sup id

noncomputable def Uof (τ : Finset (Submodule F (Fin N → F))) (sb : ℕ) : Submodule F (Fin N → F) :=
  (τ.filter (fun T : Submodule F (Fin N → F) => sb < dm T)).inf id

theorem le_Lof {τ : Finset (Submodule F (Fin N → F))} {sa : ℕ} {T : Submodule F (Fin N → F)}
    (hT : T ∈ τ) (h : dm T < sa) : T ≤ Lof τ sa :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hT, h⟩)

theorem Lof_le {τ : Finset (Submodule F (Fin N → F))} {sa : ℕ} {W : Submodule F (Fin N → F)}
    (h : ∀ T ∈ τ, dm T < sa → T ≤ W) : Lof τ sa ≤ W :=
  Finset.sup_le (fun T hT => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hT
    exact h T h1 h2)

theorem Uof_le {τ : Finset (Submodule F (Fin N → F))} {sb : ℕ} {T : Submodule F (Fin N → F)}
    (hT : T ∈ τ) (h : sb < dm T) : Uof τ sb ≤ T :=
  Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hT, h⟩)

theorem le_Uof {τ : Finset (Submodule F (Fin N → F))} {sb : ℕ} {W : Submodule F (Fin N → F)}
    (h : ∀ T ∈ τ, sb < dm T → W ≤ T) : W ≤ Uof τ sb :=
  Finset.le_inf (fun T hT => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hT
    exact h T h1 h2)

theorem ok_iff (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa (sa + 1)) (W : Submodule F (Fin N → F)) :
    OkV lo m τ W ↔ (dm W = sa ∨ dm W = sa + 1) ∧ Lof τ sa ≤ W ∧ W ≤ Uof τ (sa + 1) := by
  constructor
  · intro hW
    have hd := ok_dim lo m τ sa (sa + 1) D.hT D.hex hW
    refine ⟨hd, Lof_le (fun T hT h => le_of_ok_lt lo m τ hW hT (by omega)),
      le_Uof (fun T hT h => ge_of_ok_lt lo m τ hW hT (by omega))⟩
  · rintro ⟨hd, hL, hU⟩
    have hWτ : W ∉ τ := by
      intro hW
      have := D.hT W hW
      omega
    have hcmp : ∀ T ∈ τ, W ≤ T ∨ T ≤ W := by
      intro T hT
      have h1 := D.hT T hT
      by_cases hlt : dm T < sa
      · exact Or.inr ((le_Lof hT hlt).trans hL)
      · have : sa + 1 < dm T := by omega
        exact Or.inl (hU.trans (Uof_le hT this))
    refine ⟨hWτ, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · have := D.hsa; have := D.hsb; omega
      · exact hτ.1 x hx
    · intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Or.inl le_rfl
      · exact hcmp y hy
      · exact (hcmp x hx).symm
      · exact hτ.2 x hx y hy

theorem dm_Lof_pos (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa (sa + 1)) (h : lo < sa) :
    dm (Lof τ sa) + 1 = sa := by
  obtain ⟨T, hT, hTd⟩ := D.hex (sa - 1) (by omega) (by have := D.hsb; omega) (by omega) (by omega)
  have h1 : T ≤ Lof τ sa := le_Lof hT (by omega)
  have h2 : Lof τ sa ≤ T := Lof_le (fun T' hT' hlt =>
    le_of_cmp_dim (hτ.2 T' hT' T hT) (by omega))
  have : Lof τ sa = T := le_antisymm h2 h1
  rw [this]; omega

theorem Lof_zero (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hτ : IsFl lo m τ) (h : sa = lo) : Lof τ sa = ⊥ := by
  apply le_antisymm _ bot_le
  apply Lof_le
  intro T hT hlt
  have := (hτ.1 T hT).1
  omega

theorem dm_Uof (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa (sa + 1)) (h : sa + 1 < lo + m) :
    dm (Uof τ (sa + 1)) = sa + 2 := by
  obtain ⟨T, hT, hTd⟩ := D.hex (sa + 2) (by have := D.hsa; omega) (by omega) (by omega) (by omega)
  have h1 : Uof τ (sa + 1) ≤ T := Uof_le hT (by omega)
  have h2 : T ≤ Uof τ (sa + 1) := le_Uof (fun T' hT' hlt =>
    le_of_cmp_dim (hτ.2 T hT T' hT') (by omega))
  have : Uof τ (sa + 1) = T := le_antisymm h1 h2
  rw [this]; omega

theorem Uof_top (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hτ : IsFl lo m τ) (h : sa + 1 = lo + m) : Uof τ (sa + 1) = ⊤ := by
  apply le_antisymm le_top
  apply le_Uof
  intro T hT hlt
  have := (hτ.1 T hT).2
  omega


def IncConcl (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (d1 d2 : ℕ) : Prop :=
  d1 ≠ d2 ∧ (∀ W, OkV lo m τ W → dm W = d1 ∨ dm W = d2) ∧
  (∀ W1 W2, OkV lo m τ W1 → OkV lo m τ W2 → dm W1 = d1 → dm W2 = d1 → W1 ≠ W2 →
      ∃! W', OkV lo m τ W' ∧ Cmp W1 W' ∧ Cmp W2 W') ∧
  (∀ W, OkV lo m τ W → dm W = d2 →
      Set.ncard {W' | OkV lo m τ W' ∧ Cmp W W'} = Fintype.card F + 1) ∧
  (∀ W, OkV lo m τ W → ∃ W', OkV lo m τ W' ∧ Cmp W W')

theorem nonempty_of_count {S : Set (Submodule F (Fin N → F))}
    (h : S.ncard = Fintype.card F + 1) : ∃ W', W' ∈ S := by
  by_contra hne
  push Not at hne
  have : S = ∅ := Set.eq_empty_iff_forall_notMem.2 hne
  rw [this, Set.ncard_empty] at h
  omega

theorem type_P (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hhi : lo + m < N)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa (sa + 1)) (h : lo < sa) :
    IncConcl lo m τ sa (sa + 1) := by
  have hL := dm_Lof_pos lo m τ sa hτ D h
  have hU : sa < dm (Uof τ (sa + 1)) := by
    by_cases hc : sa + 1 < lo + m
    · rw [dm_Uof lo m τ sa hτ D hc]; omega
    · rw [Uof_top lo m τ sa hτ (by have := D.hsb; omega)]
      simp only [finrank_top, Module.finrank_fin_fun]
      have := D.hsb
      omega
  have hok := ok_iff lo m τ sa hτ D
  have hdeg : ∀ W, OkV lo m τ W → dm W = sa + 1 →
      Set.ncard {W' | OkV lo m τ W' ∧ Cmp W W'} = Fintype.card F + 1 := by
    intro W hW hd
    have hW' := (hok W).1 hW
    rw [← card_middle (Lof τ sa) W hW'.2.1 (by omega)]
    congr 1
    ext M
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hM, hc⟩
      have hMd := (hok M).1 hM
      have hdne := dim_ne_of_cmp hc
      have hMle : M ≤ W := by
        rcases hc.2 with h1 | h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
        · exact h1
      exact ⟨hMd.2.1, hMle, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      have hM : OkV lo m τ M := (hok M).2 ⟨Or.inl (by omega), h1, h2.trans hW'.2.2⟩
      refine ⟨hM, ?_, Or.inr h2⟩
      intro he
      rw [← he] at h3; omega
  refine ⟨by omega, fun W hW => ?_, ?_, ?_, ?_⟩
  · exact ((hok W).1 hW).1
  · intro W1 W2 h1 h2 hd1 hd2 hne
    have hW1 := (hok W1).1 h1
    have hW2 := (hok W2).1 h2
    have hsup : dm (↥(W1 ⊔ W2 : Submodule F (Fin N → F))) = sa + 1 := by
      have e1 : W1 < W1 ⊔ W2 := by
        refine lt_of_le_of_ne le_sup_left (fun he => hne ?_)
        have : W2 ≤ W1 := by rw [he]; exact le_sup_right
        exact (Submodule.eq_of_le_of_finrank_eq this (by omega)).symm
      have e2 := Submodule.finrank_lt_finrank_of_lt e1
      have e3 := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
      have e4 : dm (↥(Lof τ sa)) ≤ dm (↥(W1 ⊓ W2 : Submodule F (Fin N → F))) :=
        Submodule.finrank_mono (le_inf hW1.2.1 hW2.2.1)
      omega
    have hW' : OkV lo m τ (W1 ⊔ W2) := (hok _).2 ⟨Or.inr hsup, hW1.2.1.trans le_sup_left,
      sup_le hW1.2.2 hW2.2.2⟩
    refine ⟨W1 ⊔ W2, ⟨hW', ⟨fun he => ?_, Or.inl le_sup_left⟩, ⟨fun he => ?_, Or.inl le_sup_right⟩⟩, ?_⟩
    · rw [← he] at hsup; omega
    · rw [← he] at hsup; omega
    · rintro W'' ⟨hW'', c1, c2⟩
      have hd'' := ((hok W'').1 hW'').1
      have hdne := dim_ne_of_cmp c1
      have hle1 : W1 ≤ W'' := by
        rcases c1.2 with h1 | h1
        · exact h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
      have hle2 : W2 ≤ W'' := by
        rcases c2.2 with h1 | h1
        · exact h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
      have hle := sup_le hle1 hle2
      exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  · intro W hW hd
    exact hdeg W hW hd
  · intro W hW
    have hW' := (hok W).1 hW
    rcases hW'.1 with hd | hd
    · obtain ⟨M, h1, h2, h3⟩ := exists_cover hW'.2.2 (by omega)
      have hM : OkV lo m τ M := (hok M).2 ⟨Or.inr (by omega), hW'.2.1.trans h1, h2⟩
      exact ⟨M, hM, fun he => by rw [← he] at h3; omega, Or.inl h1⟩
    · obtain ⟨M, hM⟩ := nonempty_of_count (hdeg W hW hd)
      exact ⟨M, hM⟩

theorem type_H (lo m : ℕ) (τ : Finset (Submodule F (Fin N → F))) (sa : ℕ)
    (hm : 2 ≤ m)
    (hτ : IsFl lo m τ) (D : TauData lo m τ sa (sa + 1)) (h : sa = lo) :
    IncConcl lo m τ (sa + 1) sa := by
  have hL : Lof τ sa = ⊥ := Lof_zero lo m τ sa hτ h
  have hU : dm (Uof τ (sa + 1)) = sa + 2 := dm_Uof lo m τ sa hτ D (by omega)
  have hok := ok_iff lo m τ sa hτ D
  have hdeg : ∀ W, OkV lo m τ W → dm W = sa →
      Set.ncard {W' | OkV lo m τ W' ∧ Cmp W W'} = Fintype.card F + 1 := by
    intro W hW hd
    have hW' := (hok W).1 hW
    rw [← card_middle W (Uof τ (sa + 1)) hW'.2.2 (by omega)]
    congr 1
    ext M
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hM, hc⟩
      have hMd := (hok M).1 hM
      have hdne := dim_ne_of_cmp hc
      have hMle : W ≤ M := by
        rcases hc.2 with h1 | h1
        · exact h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
      exact ⟨hMle, hMd.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      have hM : OkV lo m τ M := (hok M).2 ⟨Or.inr (by omega), hL ▸ bot_le, h2⟩
      refine ⟨hM, ?_, Or.inl h1⟩
      intro he
      rw [← he] at h3; omega
  refine ⟨by omega, fun W hW => ?_, ?_, ?_, ?_⟩
  · rcases ((hok W).1 hW).1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro W1 W2 h1 h2 hd1 hd2 hne
    have hW1 := (hok W1).1 h1
    have hW2 := (hok W2).1 h2
    have hsup : dm (↥(W1 ⊔ W2 : Submodule F (Fin N → F))) = sa + 2 := by
      have e1 : W1 < W1 ⊔ W2 := by
        refine lt_of_le_of_ne le_sup_left (fun he => hne ?_)
        have : W2 ≤ W1 := by rw [he]; exact le_sup_right
        exact (Submodule.eq_of_le_of_finrank_eq this (by omega)).symm
      have e2 := Submodule.finrank_lt_finrank_of_lt e1
      have e4 : dm (↥(W1 ⊔ W2 : Submodule F (Fin N → F))) ≤ dm (↥(Uof τ (sa + 1))) :=
        Submodule.finrank_mono (sup_le hW1.2.2 hW2.2.2)
      omega
    have e3 := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
    have hinf : dm (↥(W1 ⊓ W2 : Submodule F (Fin N → F))) = sa := by omega
    have hW' : OkV lo m τ (W1 ⊓ W2) := (hok _).2 ⟨Or.inl hinf, hL ▸ bot_le,
      inf_le_left.trans hW1.2.2⟩
    refine ⟨W1 ⊓ W2, ⟨hW', ⟨fun he => ?_, Or.inr inf_le_left⟩, ⟨fun he => ?_, Or.inr inf_le_right⟩⟩, ?_⟩
    · rw [← he] at hinf; omega
    · rw [← he] at hinf; omega
    · rintro W'' ⟨hW'', c1, c2⟩
      have hd'' := ((hok W'').1 hW'').1
      have hdne := dim_ne_of_cmp c1
      have hle1 : W'' ≤ W1 := by
        rcases c1.2 with h1 | h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
        · exact h1
      have hle2 : W'' ≤ W2 := by
        rcases c2.2 with h1 | h1
        · exact absurd (Submodule.finrank_mono h1) (by omega)
        · exact h1
      have hle := le_inf hle1 hle2
      exact (Submodule.eq_of_le_of_finrank_eq hle (by omega))
  · intro W hW hd
    exact hdeg W hW hd
  · intro W hW
    have hW' := (hok W).1 hW
    rcases hW'.1 with hd | hd
    · obtain ⟨M, hM⟩ := nonempty_of_count (hdeg W hW hd)
      exact ⟨M, hM⟩
    · obtain ⟨M, h1, h2⟩ := exists_sub W sa (by omega)
      have hM : OkV lo m τ M := (hok M).2 ⟨Or.inl h2, hL ▸ bot_le, h1.trans hW'.2.2⟩
      exact ⟨M, hM, ⟨fun he => by rw [← he] at h2; omega, Or.inr h1⟩⟩

end Geom

section Final
variable {F : Type*} [Field F] [Fintype F] {N : ℕ} [DecidableEq (Submodule F (Fin N → F))]

theorem nonneg_bound : 0 ≤ 2 / (Real.sqrt (Fintype.card F) - 1) := by
  have hq : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have : (1 : ℝ) < Real.sqrt (Fintype.card F) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  exact div_nonneg (by norm_num) (by linarith)

theorem topLink_abstract (lo m : ℕ) (hm : 2 ≤ m) (hhi : lo + m < N)
    (X : Finset (Finset (Submodule F (Fin N → F)))) (hX : ∀ s, s ∈ X ↔ IsFl lo m s)
    (τ : Finset (Submodule F (Fin N → F))) (hτ : τ ∈ X) (hcard : τ.card + 2 = m + 1) :
    lambdaTau X τ ≤ 2 / (Real.sqrt (Fintype.card F) - 1) := by
  have hτfl : IsFl lo m τ := (hX τ).1 hτ
  obtain ⟨sa, sb, hlt, hsa, hsb, hT, hex⟩ := tau_dims lo m τ hτfl hcard
  have D : TauData lo m τ sa sb := ⟨hlt, hsa, hsb, hT, hex⟩
  obtain ⟨w, hinj, hsurj, hOk, hadj⟩ := link_data lo m X hX τ hτ
  unfold lambdaTau
  classical
  rcases Nat.lt_or_ge (sa + 1) sb with h1 | h1
  · refine le_trans (bip_transport (skeleton1 (link X τ)) w (OkV lo m τ) hOk hadj sa
      (case_one lo m τ sa sb hτfl D h1)) nonneg_bound
  · have hsb' : sb = sa + 1 := by omega
    subst hsb'
    by_cases hl : lo < sa
    · obtain ⟨hne, hdim, hone, hdeg, hpos⟩ := type_P lo m τ sa hhi hτfl D hl
      exact incidence_transport (skeleton1 (link X τ)) w hinj (OkV lo m τ) hsurj hOk hadj
        _ _ hne hdim hone hdeg hpos
    · have hl' : sa = lo := by omega
      obtain ⟨hne, hdim, hone, hdeg, hpos⟩ := type_H lo m τ sa hm hτfl D hl'
      exact incidence_transport (skeleton1 (link X τ)) w hinj (OkV lo m τ) hsurj hOk hadj
        _ _ hne hdim hone hdeg hpos

theorem flags_topLink (F : Type*) [Field F] [Fintype F] (r k : ℕ)
    [DecidableEq (Submodule F (Fin (2 * r) → F))] (hk : 1 ≤ k) (hkr : k < r) :
    IsTopLinkExpander (flagsComplex F r k) (2 * k + 1)
      (2 / (Real.sqrt (Fintype.card F) - 1)) := by
  intro τ hτ hcard
  have hX : ∀ s, s ∈ flagsComplex F r k ↔ IsFl (r - k) (2 * k) s := by
    intro s
    unfold flagsComplex IsFl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e : r - k + 2 * k = r + k := by omega
    rw [e]
  exact topLink_abstract (r - k) (2 * k) (by omega) (by omega) _ hX τ hτ (by omega)

end Final
end SteurerHDX.Dev.Flags
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open SteurerHDX

namespace SteurerHDX.Dev.Flags2

variable {F : Type*} [Field F] [Fintype F] {N : ℕ}

theorem exists_cover {C E : Submodule F (Fin N → F)} (hCE : C ≤ E)
    (hlt : Module.finrank F C < Module.finrank F E) :
    ∃ M, C ≤ M ∧ M ≤ E ∧ Module.finrank F M = Module.finrank F C + 1 := by
  have hne : C < E := lt_of_le_of_ne hCE (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)
  obtain ⟨v, hvE, hvC⟩ := SetLike.exists_of_lt hne
  have hlt2 : C < C ⊔ Submodule.span F ({v} : Set (Fin N → F)) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hvC
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt2
  have h3 : Module.finrank F (Submodule.span F ({v} : Set (Fin N → F))) ≤ 1 := by
    have := finrank_span_finset_le_card (R := F) ({v} : Finset (Fin N → F))
    rw [Finset.coe_singleton, Finset.card_singleton] at this
    exact this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank C (Submodule.span F ({v} : Set (Fin N → F)))
  exact ⟨C ⊔ Submodule.span F ({v} : Set (Fin N → F)), le_sup_left,
    sup_le hCE ((Submodule.span_singleton_le_iff_mem _ _).2 hvE), by omega⟩

/-- intermediate subspaces of every prescribed dimension -/
theorem exists_between {A B : Submodule F (Fin N → F)} (hAB : A ≤ B) (e : ℕ)
    (he : e ≤ Module.finrank F B - Module.finrank F A) :
    ∃ M, A ≤ M ∧ M ≤ B ∧ Module.finrank F M = Module.finrank F A + e := by
  have hle := Submodule.finrank_mono hAB
  induction e with
  | zero => exact ⟨A, le_rfl, hAB, by simp⟩
  | succ e ih =>
    obtain ⟨M, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨M', h4, h5, h6⟩ := exists_cover h2 (by omega)
    exact ⟨M', h1.trans h4, h5, by omega⟩

theorem le_of_cmp_dim {A B : Submodule F (Fin N → F)} (h : A ≤ B ∨ B ≤ A)
    (hd : Module.finrank F A ≤ Module.finrank F B) : A ≤ B := by
  rcases h with h | h
  · exact h
  · exact (Submodule.eq_of_le_of_finrank_eq h (le_antisymm (Submodule.finrank_mono h) hd)).ge

theorem eq_of_cmp_dim_eq {A B : Submodule F (Fin N → F)} (h : A ≤ B ∨ B ≤ A)
    (hd : Module.finrank F A = Module.finrank F B) : A = B := by
  rcases h with h | h
  · exact Submodule.eq_of_le_of_finrank_eq h hd
  · exact (Submodule.eq_of_le_of_finrank_eq h hd.symm).symm

variable (F) in
theorem mem_flags (r k : ℕ) (σ : Finset (Submodule F (Fin (2 * r) → F))) :
    σ ∈ flagsComplex F r k ↔
      ((∀ W ∈ σ, r - k ≤ Module.finrank F W ∧ Module.finrank F W ≤ r + k) ∧
        (∀ W ∈ σ, ∀ W' ∈ σ, W ≤ W' ∨ W' ≤ W)) := by
  unfold flagsComplex
  simp

/-- chain members with equal dimension coincide, so dim is injective on a face -/
theorem card_eq_image (r k : ℕ) (σ : Finset (Submodule F (Fin (2 * r) → F)))
    (h : σ ∈ flagsComplex F r k) :
    (σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W)).card = σ.card := by
  rw [mem_flags] at h
  apply Finset.card_image_of_injOn
  intro W hW W' hW' hd
  exact eq_of_cmp_dim_eq (h.2 W hW W' hW') hd

theorem image_subset (r k : ℕ) (σ : Finset (Submodule F (Fin (2 * r) → F)))
    (h : σ ∈ flagsComplex F r k) :
    σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) ⊆ Finset.Icc (r - k) (r + k) := by
  rw [mem_flags] at h
  intro t ht
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 ht
  have := h.1 W hW
  simp only [Finset.mem_Icc]
  exact this

theorem card_Icc_flags (r k : ℕ) (hk : k < r) : (Finset.Icc (r - k) (r + k)).card = 2 * k + 1 := by
  rw [Nat.card_Icc]; omega

theorem simplicial (r k : ℕ) : IsSimplicialComplex (flagsComplex F r k) := by
  intro τ hτ σ hσ
  rw [mem_flags] at hτ ⊢
  exact ⟨fun W hW => hτ.1 W (hσ hW), fun W hW W' hW' => hτ.2 W (hσ hW) W' (hσ hW')⟩

/-- a maximal face has all dimensions -/
theorem maximal_image (r : ℕ) [DecidableEq (Submodule F (Fin (2 * r) → F))] (k : ℕ) (hk : k < r)
    (σ : Finset (Submodule F (Fin (2 * r) → F))) (hσ : σ ∈ flagsComplex F r k)
    (hmax : ∀ ρ ∈ flagsComplex F r k, σ ⊆ ρ → ρ = σ) :
    σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) = Finset.Icc (r - k) (r + k) := by
  apply Finset.Subset.antisymm (image_subset r k σ hσ)
  intro t ht
  by_contra hnot
  have hσ' := (mem_flags F r k σ).1 hσ
  rw [Finset.mem_Icc] at ht
  have hnot' : ∀ C ∈ σ, Module.finrank F C ≠ t := by
    intro C hC hCt
    exact hnot (Finset.mem_image.2 ⟨C, hC, hCt⟩)
  set τ : Finset (Submodule F (Fin (2 * r) → F)) := insert ⊥ (insert ⊤ σ) with hτ
  have hdimtop : Module.finrank F (⊤ : Submodule F (Fin (2 * r) → F)) = 2 * r := by simp
  have hdimbot : Module.finrank F (⊥ : Submodule F (Fin (2 * r) → F)) = 0 := by simp
  have hcmp : ∀ C ∈ τ, ∀ D ∈ τ, C ≤ D ∨ D ≤ C := by
    intro C hC D hD
    simp only [hτ, Finset.mem_insert] at hC hD
    rcases hC with rfl | rfl | hC <;> rcases hD with rfl | rfl | hD
    all_goals first
      | exact Or.inl le_rfl
      | exact Or.inl bot_le
      | exact Or.inr bot_le
      | exact Or.inl le_top
      | exact Or.inr le_top
      | exact hσ'.2 _ hC _ hD
  have hlow : (τ.filter (fun C : Submodule F (Fin (2 * r) → F) => Module.finrank F C < t)).Nonempty :=
    ⟨⊥, Finset.mem_filter.2 ⟨by simp [hτ], by rw [hdimbot]; omega⟩⟩
  have hup : (τ.filter (fun C : Submodule F (Fin (2 * r) → F) => t < Module.finrank F C)).Nonempty :=
    ⟨⊤, Finset.mem_filter.2 ⟨by simp [hτ], by rw [hdimtop]; omega⟩⟩
  obtain ⟨A, hA, hAmax⟩ := Finset.exists_max_image _ (fun C : Submodule F (Fin (2 * r) → F) => Module.finrank F C) hlow
  obtain ⟨B, hB, hBmin⟩ := Finset.exists_min_image _ (fun C : Submodule F (Fin (2 * r) → F) => Module.finrank F C) hup
  rw [Finset.mem_filter] at hA hB
  have hAB : A ≤ B := le_of_cmp_dim (hcmp A hA.1 B hB.1) (by omega)
  obtain ⟨W, hAW, hWB, hWd⟩ := exists_between hAB (t - Module.finrank F A) (by
    have := Submodule.finrank_mono hAB
    omega)
  have hWt : Module.finrank F W = t := by omega
  have hWσ : W ∉ σ := fun h => hnot' W h hWt
  have hnew : insert W σ ∈ flagsComplex F r k := by
    rw [mem_flags]
    have hcw : ∀ C ∈ σ, C ≤ W ∨ W ≤ C := by
      intro C hC
      have hCτ : C ∈ τ := by simp [hτ, hC]
      have hne := hnot' C hC
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left
        have h1 : Module.finrank F C ≤ Module.finrank F A := hAmax C (Finset.mem_filter.2 ⟨hCτ, hlt⟩)
        exact (le_of_cmp_dim (hcmp C hCτ A hA.1) h1).trans hAW
      · right
        have h1 : Module.finrank F B ≤ Module.finrank F C := hBmin C (Finset.mem_filter.2 ⟨hCτ, hgt⟩)
        exact hWB.trans (le_of_cmp_dim (hcmp B hB.1 C hCτ) h1)
    refine ⟨?_, ?_⟩
    · intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · omega
      · exact hσ'.1 C hC
    · intro C hC D hD
      rcases Finset.mem_insert.1 hC with h1 | h1 <;> rcases Finset.mem_insert.1 hD with h2 | h2
      · rw [h1, h2]; exact Or.inl le_rfl
      · rw [h1]; exact (hcw D h2).symm
      · rw [h2]; exact hcw C h1
      · exact hσ'.2 C h1 D h2
  have := hmax _ hnew (Finset.subset_insert _ _)
  exact hWσ (this ▸ Finset.mem_insert_self W σ)

end SteurerHDX.Dev.Flags2

namespace SteurerHDX.Dev.Flags2

theorem flags_pure (F : Type*) [Field F] [Fintype F] (r k : ℕ)
    [DecidableEq (Submodule F (Fin (2 * r) → F))] (hk1 : 1 ≤ k) (hk : k < r) :
    IsPure (flagsComplex F r k) (2 * k + 1) := by
  refine ⟨simplicial r k, ?_⟩
  intro σ hσ hmax
  rw [← card_eq_image r k σ hσ, maximal_image r k hk σ hσ hmax, card_Icc_flags r k hk]

theorem flags_faces (F : Type*) [Field F] [Fintype F] (r k : ℕ)
    [DecidableEq (Submodule F (Fin (2 * r) → F))] (hk1 : 1 ≤ k) (hk : k < r) :
    ∀ σ, σ ∈ faces (flagsComplex F r k) (2 * k + 1) ↔
        σ ∈ flagsComplex F r k ∧
          σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) = Finset.Icc (r - k) (r + k) := by
  intro σ
  unfold faces
  rw [Finset.mem_filter]
  refine and_congr_right (fun hσ => ?_)
  constructor
  · intro hc
    apply Finset.eq_of_subset_of_card_le (image_subset r k σ hσ)
    rw [card_Icc_flags r k hk, card_eq_image r k σ hσ, hc]
  · intro hi
    rw [← card_eq_image r k σ hσ, hi, card_Icc_flags r k hk]

theorem flags_partite (F : Type*) [Field F] [Fintype F] (r k : ℕ)
    [DecidableEq (Submodule F (Fin (2 * r) → F))] (hk1 : 1 ≤ k) (hk : k < r) :
    IsPartite (flagsComplex F r k) (2 * k + 1) := by
  let c : Submodule F (Fin (2 * r) → F) → Fin (2 * k + 1) :=
    fun W => ⟨min (Module.finrank F W - (r - k)) (2 * k), by omega⟩
  refine ⟨c, ?_⟩
  intro σ hσ i
  obtain ⟨hσX, himg⟩ := (flags_faces F r k hk1 hk σ).1 hσ
  have hσ' := (mem_flags F r k σ).1 hσX
  have hc : ∀ W ∈ σ, (c W : ℕ) = Module.finrank F W - (r - k) := by
    intro W hW
    have := hσ'.1 W hW
    show min _ _ = _
    omega
  have hi : r - k + (i : ℕ) ∈ σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) := by
    rw [himg, Finset.mem_Icc]
    have := i.2
    omega
  obtain ⟨W, hW, hWd⟩ := Finset.mem_image.1 hi
  refine ⟨W, ⟨hW, ?_⟩, ?_⟩
  · apply Fin.ext
    rw [hc W hW, hWd]
    omega
  · rintro y ⟨hy, hyc⟩
    have h1 := hc y hy
    have h2 := hσ'.1 y hy
    rw [hyc] at h1
    apply eq_of_cmp_dim_eq (hσ'.2 y hy W hW)
    omega

end SteurerHDX.Dev.Flags2
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SteurerHDX.Dev.Flags3
open Module

section Gauss
variable {F : Type*} [Field F] [Fintype F] {V : Type*} [AddCommGroup V] [Module F V] [Finite V]

theorem card_bases (U : Submodule F V) (i : ℕ) (hU : finrank F U = i) :
    Nat.card {s : Fin i → V // LinearIndependent F s ∧ Submodule.span F (Set.range s) = U} =
      ∏ j : Fin i, (Fintype.card F ^ i - Fintype.card F ^ j.val) := by
  have h1 : Nat.card {s : Fin i → V // LinearIndependent F s ∧ Submodule.span F (Set.range s) = U}
      = Nat.card {t : Fin i → U // LinearIndependent F t} := by
    apply Nat.card_congr
    refine
      { toFun := fun s => ⟨fun j => ⟨s.1 j, by
            have := Submodule.subset_span (R := F) (s := Set.range s.1) ⟨j, rfl⟩
            rwa [s.2.2] at this⟩, ?_⟩
        invFun := fun t => ⟨fun j => (t.1 j : V), ?_, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
    · apply LinearIndependent.of_comp U.subtype
      exact s.2.1
    · exact t.2.map' U.subtype (Submodule.ker_subtype U)
    · have htop : Submodule.span F (Set.range t.1) = ⊤ :=
        t.2.span_eq_top_of_card_eq_finrank' (by simp [hU])
      have : Set.range (fun j => (t.1 j : V)) = U.subtype '' Set.range t.1 := by
        ext x; simp
      rw [this, ← Submodule.map_span, htop, Submodule.map_top, Submodule.range_subtype]
  rw [h1, card_linearIndependent (by simp [hU])]
  simp [hU]

theorem gauss_count (i : ℕ) (hi : i ≤ finrank F V) :
    Nat.card {U : Submodule F V // finrank F U = i} *
      ∏ j : Fin i, (Fintype.card F ^ i - Fintype.card F ^ j.val) =
    ∏ j : Fin i, (Fintype.card F ^ (finrank F V) - Fintype.card F ^ j.val) := by
  classical
  have : Fintype (Submodule F V) := Fintype.ofFinite _
  rw [← card_linearIndependent hi]
  let f : {s : Fin i → V // LinearIndependent F s} → {U : Submodule F V // finrank F U = i} :=
    fun s => ⟨Submodule.span F (Set.range s.1), by
      rw [finrank_span_eq_card s.2]; simp⟩
  have h2 : Nat.card {s : Fin i → V // LinearIndependent F s} =
      ∑ y : {U : Submodule F V // finrank F U = i}, Nat.card {x // f x = y} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  have h3 : ∀ y : {U : Submodule F V // finrank F U = i}, Nat.card {x // f x = y} =
      ∏ j : Fin i, (Fintype.card F ^ i - Fintype.card F ^ j.val) := by
    intro y
    rw [← card_bases y.1 i y.2]
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun s => ⟨⟨s.1, s.2.1⟩, Subtype.ext s.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun s => rfl }
  rw [h2]
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card]

theorem q_two_le : 2 ≤ Fintype.card F := by
  have : Nontrivial F := inferInstance
  exact Fintype.one_lt_card

theorem gauss_bounds (i : ℕ) (hi : i ≤ finrank F V) :
    Fintype.card F ^ ((finrank F V - i) * i) ≤
      Nat.card {U : Submodule F V // finrank F U = i} ∧
    Nat.card {U : Submodule F V // finrank F U = i} ≤
      2 ^ i * Fintype.card F ^ ((finrank F V - i) * i) := by
  have hg := gauss_count (F := F) (V := V) i hi
  set N := Nat.card {U : Submodule F V // finrank F U = i} with hN
  set q := Fintype.card F with hq
  set n := finrank F V with hn
  have hq2 : 2 ≤ q := q_two_le
  have hqpos : 0 < q := by omega
  have hP : 0 < ∏ j : Fin i, (q ^ i - q ^ j.val) := by
    apply Finset.prod_pos
    intro j _
    have : q ^ j.val < q ^ i := Nat.pow_lt_pow_right (by omega) j.2
    omega
  have hn' : q ^ n = q ^ (n - i) * q ^ i := by
    rw [← pow_add]; congr 1; omega
  have hlow : ∀ j : Fin i, q ^ (n - i) * (q ^ i - q ^ j.val) ≤ q ^ n - q ^ j.val := by
    intro j
    have h1 : 1 ≤ q ^ (n - i) := Nat.one_le_pow _ _ hqpos
    have h2 : q ^ j.val ≤ q ^ (n - i) * q ^ j.val := Nat.le_mul_of_pos_left _ h1
    rw [Nat.mul_sub, ← hn']
    have : q ^ (n - i) * q ^ i ≥ q ^ (n - i) * q ^ j.val :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hqpos j.2.le)
    omega
  have hup : ∀ j : Fin i, q ^ n - q ^ j.val ≤ 2 * q ^ (n - i) * (q ^ i - q ^ j.val) := by
    intro j
    have h3 : q ^ (j.val + 1) ≤ q ^ i := Nat.pow_le_pow_right hqpos j.2
    have h4 : 2 * q ^ j.val ≤ q ^ (j.val + 1) := by
      rw [pow_succ]; nlinarith [Nat.zero_le (q ^ j.val)]
    have h5 : q ^ i ≤ 2 * (q ^ i - q ^ j.val) := by omega
    calc q ^ n - q ^ j.val ≤ q ^ n := Nat.sub_le _ _
      _ = q ^ (n - i) * q ^ i := hn'
      _ ≤ q ^ (n - i) * (2 * (q ^ i - q ^ j.val)) := Nat.mul_le_mul_left _ h5
      _ = _ := by ring
  have hlowP : q ^ ((n - i) * i) * ∏ j : Fin i, (q ^ i - q ^ j.val) ≤
      ∏ j : Fin i, (q ^ n - q ^ j.val) := by
    calc q ^ ((n - i) * i) * ∏ j : Fin i, (q ^ i - q ^ j.val)
        = ∏ j : Fin i, (q ^ (n - i) * (q ^ i - q ^ j.val)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul]
      _ ≤ _ := Finset.prod_le_prod' (fun j _ => hlow j)
  have hupP : ∏ j : Fin i, (q ^ n - q ^ j.val) ≤
      2 ^ i * q ^ ((n - i) * i) * ∏ j : Fin i, (q ^ i - q ^ j.val) := by
    calc ∏ j : Fin i, (q ^ n - q ^ j.val)
        ≤ ∏ j : Fin i, (2 * q ^ (n - i) * (q ^ i - q ^ j.val)) :=
          Finset.prod_le_prod' (fun j _ => hup j)
      _ = 2 ^ i * q ^ ((n - i) * i) * ∏ j : Fin i, (q ^ i - q ^ j.val) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  constructor
  · rw [← hg] at hlowP
    exact Nat.le_of_mul_le_mul_right hlowP hP
  · rw [← hg] at hupP
    exact Nat.le_of_mul_le_mul_right hupP hP

end Gauss
section Steps
variable {F : Type*} [Field F] [Fintype F] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem exists_up (T U : Submodule F V) (hle : T ≤ U) (h : finrank F U = finrank F T + 1) :
    ∃ v : V, U = T ⊔ Submodule.span F {v} := by
  have hlt : T < U := by
    refine lt_of_le_of_ne hle ?_
    rintro rfl; omega
  obtain ⟨v, hvU, hvT⟩ := SetLike.exists_of_lt hlt
  refine ⟨v, ?_⟩
  have h1 : T ⊔ Submodule.span F {v} ≤ U :=
    sup_le hle ((Submodule.span_singleton_le_iff_mem v U).2 hvU)
  have h2 : T < T ⊔ Submodule.span F {v} := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    apply hvT
    rw [he]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have h3 := Submodule.finrank_lt_finrank_of_lt h2
  have h4 := Submodule.finrank_mono h1
  exact (Submodule.eq_of_le_of_finrank_le h1 (by omega)).symm

theorem exists_down (T U : Submodule F V) (hle : T ≤ U) (h : finrank F U = finrank F T + 1) :
    ∃ g : Module.Dual F V, T = U ⊓ LinearMap.ker g := by
  have hlt : T < U := by
    refine lt_of_le_of_ne hle ?_
    rintro rfl; omega
  obtain ⟨v, hvU, hvT⟩ := SetLike.exists_of_lt hlt
  obtain ⟨g, hgv, hg⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvT inferInstance
  refine ⟨g, ?_⟩
  have hTk : T ≤ LinearMap.ker g := by
    intro x hx
    have : g x ∈ T.map g := Submodule.mem_map_of_mem hx
    rw [hg] at this
    simpa using this
  have h1 : T ≤ U ⊓ LinearMap.ker g := le_inf hle hTk
  have h2 : U ⊓ LinearMap.ker g < U := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    have : v ∈ U ⊓ LinearMap.ker g := by rw [he]; exact hvU
    exact hgv (LinearMap.mem_ker.1 this.2)
  have h3 := Submodule.finrank_lt_finrank_of_lt h2
  exact (Submodule.eq_of_le_of_finrank_le h1 (by omega))

end Steps

section Pi
variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

/-- The functional with coefficient vector `c`. -/
noncomputable def phi (c : Fin n → F) : Module.Dual F (Fin n → F) :=
  ∑ i, c i • LinearMap.proj i

theorem exists_phi (g : Module.Dual F (Fin n → F)) : ∃ c : Fin n → F, g = phi c := by
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ g x]
  simp [phi, LinearMap.sum_apply, mul_comm]

theorem exists_down' (T U : Submodule F (Fin n → F)) (hle : T ≤ U)
    (h : finrank F U = finrank F T + 1) :
    ∃ c : Fin n → F, T = U ⊓ LinearMap.ker (phi c) := by
  obtain ⟨g, hg⟩ := exists_down T U hle h
  obtain ⟨c, rfl⟩ := exists_phi g
  exact ⟨c, hg⟩

end Pi

section Chain
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The member of `σ` of dimension `j` (junk `⊥` if there is none). -/
noncomputable def dimSup (σ : Finset (Submodule F V)) (j : ℕ) : Submodule F V :=
  (σ.filter (fun U : Submodule F V => finrank F U = j)).sup id

/-- A chain with one member of each dimension in `[a, b]`. -/
structure IsFullChain (a b : ℕ) (σ : Finset (Submodule F V)) : Prop where
  dims : ∀ U ∈ σ, a ≤ finrank F U ∧ finrank F U ≤ b
  chain : ∀ U ∈ σ, ∀ U' ∈ σ, U ≤ U' ∨ U' ≤ U
  card : σ.card = (Finset.Icc a b).card

variable {a b : ℕ} {σ : Finset (Submodule F V)}

theorem IsFullChain.eq_of_dim (hc : IsFullChain a b σ) {U U' : Submodule F V} (hU : U ∈ σ)
    (hU' : U' ∈ σ) (h : finrank F U = finrank F U') : U = U' := by
  rcases hc.chain U hU U' hU' with hle | hle
  · exact Submodule.eq_of_le_of_finrank_eq hle h
  · exact (Submodule.eq_of_le_of_finrank_eq hle h.symm).symm

theorem dimSup_of_mem (hc : IsFullChain a b σ) {U : Submodule F V} (hU : U ∈ σ) :
    dimSup σ (finrank F U) = U := by
  unfold dimSup
  have : σ.filter (fun U' : Submodule F V => finrank F U' = finrank F U) = {U} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_filter.2 ⟨hU, rfl⟩, fun U' hU' => ?_⟩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hU'
    exact hc.eq_of_dim h1 hU h2
  rw [this, Finset.sup_singleton]; rfl

theorem IsFullChain.exists_dim (hc : IsFullChain a b σ) {j : ℕ} (hj : j ∈ Finset.Icc a b) :
    ∃ U ∈ σ, finrank F U = j := by
  have hsub : σ.image (fun U : Submodule F V => finrank F U) ⊆ Finset.Icc a b := by
    intro x hx
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_Icc.2 (hc.dims U hU)
  have hinj : Set.InjOn (fun U : Submodule F V => finrank F U) (σ : Set (Submodule F V)) :=
    fun U hU U' hU' h => hc.eq_of_dim hU hU' h
  have hcard : (Finset.Icc a b).card ≤ (σ.image (fun U : Submodule F V => finrank F U)).card := by
    rw [Finset.card_image_of_injOn hinj, hc.card]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← this] at hj
  obtain ⟨U, hU, h⟩ := Finset.mem_image.1 hj
  exact ⟨U, hU, h⟩

theorem IsFullChain.dimSup_spec (hc : IsFullChain a b σ) {j : ℕ} (hj : j ∈ Finset.Icc a b) :
    dimSup σ j ∈ σ ∧ finrank F (dimSup σ j) = j := by
  obtain ⟨U, hU, rfl⟩ := hc.exists_dim hj
  rw [dimSup_of_mem hc hU]
  exact ⟨hU, rfl⟩

theorem IsFullChain.eq_image (hc : IsFullChain a b σ) :
    σ = (Finset.Icc a b).image (dimSup σ) := by
  ext U
  constructor
  · intro hU
    refine Finset.mem_image.2 ⟨finrank F U, Finset.mem_Icc.2 (hc.dims U hU), ?_⟩
    exact dimSup_of_mem hc hU
  · intro hU
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hU
    exact (hc.dimSup_spec hj).1

theorem IsFullChain.le_succ (hc : IsFullChain a b σ) {j : ℕ} (hj : j ∈ Finset.Icc a b)
    (hj' : j + 1 ∈ Finset.Icc a b) : dimSup σ j ≤ dimSup σ (j + 1) := by
  obtain ⟨h1, h2⟩ := hc.dimSup_spec hj
  obtain ⟨h3, h4⟩ := hc.dimSup_spec hj'
  rcases hc.chain _ h1 _ h3 with h | h
  · exact h
  · have := Submodule.finrank_mono h
    omega

end Chain

section Encode
variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

open Classical in
/-- A vector `v` with `U = T ⊔ span {v}`, if there is one. -/
noncomputable def upVec (T U : Submodule F (Fin n → F)) : Fin n → F :=
  if h : ∃ v : Fin n → F, U = T ⊔ Submodule.span F {v} then h.choose else 0

open Classical in
/-- A vector `c` with `T = U ⊓ ker (phi c)`, if there is one. -/
noncomputable def downVec (U T : Submodule F (Fin n → F)) : Fin n → F :=
  if h : ∃ c : Fin n → F, T = U ⊓ LinearMap.ker (phi c) then h.choose else 0

theorem upVec_spec {T U : Submodule F (Fin n → F)} (h : ∃ v : Fin n → F, U = T ⊔ Submodule.span F {v}) :
    U = T ⊔ Submodule.span F {upVec T U} := by
  unfold upVec; rw [dif_pos h]; exact h.choose_spec

theorem downVec_spec {U T : Submodule F (Fin n → F)}
    (h : ∃ c : Fin n → F, T = U ⊓ LinearMap.ker (phi c)) :
    T = U ⊓ LinearMap.ker (phi (downVec U T)) := by
  unfold downVec; rw [dif_pos h]; exact h.choose_spec

open Classical in
/-- Encoding of the `j`-th step of a chain, relative to the base dimension `j0`. -/
noncomputable def ez (j0 : ℕ) (σ : Finset (Submodule F (Fin n → F))) (j : ℕ) : Fin n → F :=
  if j0 < j then upVec (dimSup σ (j - 1)) (dimSup σ j)
  else if j < j0 then downVec (dimSup σ (j + 1)) (dimSup σ j) else 0

variable {a b : ℕ}

theorem dimSup_eq_of_ez {σ σ' : Finset (Submodule F (Fin n → F))} (hc : IsFullChain a b σ)
    (hc' : IsFullChain a b σ') {W : Submodule F (Fin n → F)} (hW : W ∈ σ) (hW' : W ∈ σ')
    (hj0 : finrank F W ∈ Finset.Icc a b)
    (he : ∀ j ∈ Finset.Icc a b, ez (finrank F W) σ j = ez (finrank F W) σ' j) :
    ∀ j ∈ Finset.Icc a b, dimSup σ j = dimSup σ' j := by
  set j0 := finrank F W with hj0def
  have hbase : dimSup σ j0 = dimSup σ' j0 := by
    rw [hj0def, dimSup_of_mem hc hW, dimSup_of_mem hc' hW']
  have hup : ∀ m, j0 + m ∈ Finset.Icc a b → dimSup σ (j0 + m) = dimSup σ' (j0 + m) := by
    intro m
    induction m with
    | zero => intro _; simpa using hbase
    | succ m ih =>
      intro hm
      have hm0 : j0 + m ∈ Finset.Icc a b := by
        simp only [Finset.mem_Icc] at hm hj0 ⊢; omega
      have ih' := ih hm0
      have hmm : j0 + (m + 1) = j0 + m + 1 := by omega
      rw [hmm] at hm ⊢
      obtain ⟨s1, s2⟩ := hc.dimSup_spec hm0
      obtain ⟨s3, s4⟩ := hc.dimSup_spec hm
      obtain ⟨t1, t2⟩ := hc'.dimSup_spec hm0
      obtain ⟨t3, t4⟩ := hc'.dimSup_spec hm
      have e1 := upVec_spec (exists_up _ _ (hc.le_succ hm0 hm) (by omega))
      have e2 := upVec_spec (exists_up _ _ (hc'.le_succ hm0 hm) (by omega))
      have ez1 := he (j0 + m + 1) hm
      have hlt : j0 < j0 + m + 1 := by omega
      simp only [ez, if_pos hlt, Nat.add_sub_cancel] at ez1
      exact e1.trans ((congrArg₂ (fun T v => T ⊔ Submodule.span F {v}) ih' ez1).trans e2.symm)
  have hdown : ∀ m, j0 - m ∈ Finset.Icc a b → dimSup σ (j0 - m) = dimSup σ' (j0 - m) := by
    intro m
    induction m with
    | zero => intro _; simpa using hbase
    | succ m ih =>
      intro hm
      have hm0 : j0 - m ∈ Finset.Icc a b := by
        simp only [Finset.mem_Icc] at hm hj0 ⊢; omega
      have ih' := ih hm0
      by_cases hmj : m < j0
      · have hj1 : j0 - (m + 1) + 1 = j0 - m := by omega
        have hm1 : j0 - (m + 1) + 1 ∈ Finset.Icc a b := by rw [hj1]; exact hm0
        obtain ⟨s1, s2⟩ := hc.dimSup_spec hm1
        obtain ⟨s3, s4⟩ := hc.dimSup_spec hm
        obtain ⟨t1, t2⟩ := hc'.dimSup_spec hm1
        obtain ⟨t3, t4⟩ := hc'.dimSup_spec hm
        have e1 := downVec_spec (exists_down' _ _ (hc.le_succ hm hm1) (by omega))
        have e2 := downVec_spec (exists_down' _ _ (hc'.le_succ hm hm1) (by omega))
        have ez1 := he (j0 - (m + 1)) hm
        have hlt : j0 - (m + 1) < j0 := by omega
        have hnlt : ¬ j0 < j0 - (m + 1) := by omega
        simp only [ez, if_neg hnlt, if_pos hlt] at ez1
        rw [hj1] at e1 e2 ez1
        exact e1.trans ((congrArg₂ (fun U c => U ⊓ LinearMap.ker (phi c)) ih' ez1).trans e2.symm)
      · have : j0 - (m + 1) = j0 - m := by omega
        rw [this]; exact ih'
  intro j hj
  by_cases h : j0 ≤ j
  · have := hup (j - j0) (by rwa [Nat.add_sub_cancel' h])
    rwa [Nat.add_sub_cancel' h] at this
  · have := hdown (j0 - j) (by rwa [Nat.sub_sub_self (by omega)])
    rwa [Nat.sub_sub_self (by omega)] at this

theorem card_chains_le (W : Submodule F (Fin n → F)) (hj0 : finrank F W ∈ Finset.Icc a b)
    (S : Finset (Finset (Submodule F (Fin n → F))))
    (hS : ∀ σ ∈ S, IsFullChain a b σ ∧ W ∈ σ) :
    S.card ≤ (Fintype.card F ^ n) ^ (Finset.Icc a b).card := by
  classical
  let f : Finset (Submodule F (Fin n → F)) → (Fin (Finset.Icc a b).card → Fin n → F) :=
    fun σ t => ez (finrank F W) σ (a + t.1)
  have hcard : (Finset.univ : Finset (Fin (Finset.Icc a b).card → Fin n → F)).card =
      (Fintype.card F ^ n) ^ (Finset.Icc a b).card := by
    simp [Fintype.card_fun]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  intro σ hσ σ' hσ' hf
  obtain ⟨hc, hW⟩ := hS σ hσ
  obtain ⟨hc', hW'⟩ := hS σ' hσ'
  have hez : ∀ j ∈ Finset.Icc a b, ez (finrank F W) σ j = ez (finrank F W) σ' j := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hlt : j - a < (Finset.Icc a b).card := by
      rw [Nat.card_Icc]; omega
    have := congrFun hf ⟨j - a, hlt⟩
    simp only [f] at this
    rwa [show a + (j - a) = j by omega] at this
  have hd := dimSup_eq_of_ez hc hc' hW hW' hj0 hez
  rw [hc.eq_image, hc'.eq_image]
  exact Finset.image_congr (fun j hj => hd j hj)

end Encode

section Complex
open SteurerHDX
variable {F : Type*} [Field F] [Fintype F] {r k : ℕ}

theorem mem_flagsComplex {σ : Finset (Submodule F (Fin (2 * r) → F))} :
    σ ∈ flagsComplex F r k ↔
      (∀ W ∈ σ, r - k ≤ finrank F W ∧ finrank F W ≤ r + k) ∧
      (∀ W ∈ σ, ∀ W' ∈ σ, W ≤ W' ∨ W' ≤ W) := by
  unfold flagsComplex
  simp

theorem facet_isFullChain (hk : k < r) {σ : Finset (Submodule F (Fin (2 * r) → F))}
    (hσ : σ ∈ faces (flagsComplex F r k) (2 * k + 1)) :
    IsFullChain (r - k) (r + k) σ := by
  obtain ⟨hX, hcard⟩ := Finset.mem_filter.1 hσ
  obtain ⟨h1, h2⟩ := mem_flagsComplex.1 hX
  refine ⟨h1, h2, ?_⟩
  rw [hcard, Nat.card_Icc]; omega

theorem degree_le [DecidableEq (Submodule F (Fin (2 * r) → F))] (hk : k < r) :
    degree (flagsComplex F r k) (2 * k + 1) ≤ (Fintype.card F ^ (2 * r)) ^ (2 * k + 1) := by
  unfold degree
  refine Finset.sup_le fun W hW => ?_
  obtain ⟨τ, hτ, hWτ⟩ := Finset.mem_biUnion.1 hW
  have hdim := (mem_flagsComplex.1 hτ).1 W hWτ
  have hj0 : finrank F W ∈ Finset.Icc (r - k) (r + k) := Finset.mem_Icc.2 hdim
  have := card_chains_le (a := r - k) (b := r + k) W hj0
    ((faces (flagsComplex F r k) (2 * k + 1)).filter (fun σ => W ∈ σ)) (fun σ hσ => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hσ
      exact ⟨facet_isFullChain hk h1, h2⟩)
  refine this.trans ?_
  rw [Nat.card_Icc]
  have : r + k + 1 - (r - k) = 2 * k + 1 := by omega
  rw [this]

/-- Vertices of dimension `i`. -/
theorem card_vertices_dim [DecidableEq (Submodule F (Fin (2 * r) → F))] (i : ℕ) (hi : r - k ≤ i ∧ i ≤ r + k) :
    (((faces (flagsComplex F r k) 1).filter
        (fun s => ∀ W ∈ s, finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℕ) =
      Nat.card {U : Submodule F (Fin (2 * r) → F) // finrank F U = i} := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun U => (⟨{U.1}, ?_⟩ : ↥((faces (flagsComplex F r k) 1).filter
        (fun s => ∀ W ∈ s, finrank F (W : Submodule F (Fin (2 * r) → F)) = i)))) ⟨?_, ?_⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_flagsComplex.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro W hW
      rw [Finset.mem_singleton.1 hW, U.2]; exact hi
    · intro W hW W' hW'
      rw [Finset.mem_singleton.1 hW, Finset.mem_singleton.1 hW']
      exact Or.inl le_rfl
    · simp
    · intro W hW
      rw [Finset.mem_singleton.1 hW]; exact U.2
  · intro U U' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Finset.singleton_injective this)
  · rintro ⟨s, hs⟩
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
    obtain ⟨_, hs3⟩ := Finset.mem_filter.1 hs1
    obtain ⟨U, rfl⟩ := Finset.card_eq_one.1 hs3
    exact ⟨⟨U, hs2 U (Finset.mem_singleton_self U)⟩, rfl⟩

theorem vertex_bounds (hk1 : 1 ≤ k) (hk : k < r) (i : ℕ) (hi : r - k ≤ i ∧ i ≤ r + k) :
    (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - 2 * k * r) ≤
        (Nat.card {U : Submodule F (Fin (2 * r) → F) // finrank F U = i} : ℝ) ∧
      (Nat.card {U : Submodule F (Fin (2 * r) → F) // finrank F U = i} : ℝ) ≤
        (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + 2 * k * r) := by
  have hfr : finrank F (Fin (2 * r) → F) = 2 * r := by simp
  obtain ⟨hlo, hup⟩ := gauss_bounds (F := F) (V := Fin (2 * r) → F) i (by rw [hfr]; omega)
  rw [hfr] at hlo hup
  have hQ2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast q_two_le (F := F)
  have hQ1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by linarith
  have hi2 : i ≤ 2 * r := by omega
  have hrk : (k : ℝ) ≤ r := by exact_mod_cast hk.le
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hik : (r : ℝ) - k ≤ i := by
    have : r - k ≤ i := hi.1
    have h2 : ((r - k : ℕ) : ℝ) ≤ i := by exact_mod_cast this
    rwa [Nat.cast_sub hk.le] at h2
  have hik2 : (i : ℝ) ≤ r + k := by exact_mod_cast hi.2
  have hsq : ((r : ℝ) - i) ^ 2 ≤ (k : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hkr : (0 : ℝ) ≤ k * r := by positivity
  have hkk : (k : ℝ) ^ 2 ≤ k * r := by nlinarith
  have hexp : (((2 * r - i) * i : ℕ) : ℝ) = (r : ℝ) ^ 2 - ((r : ℝ) - i) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hi2]; push_cast; ring
  constructor
  · calc (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - 2 * k * r)
        ≤ (Fintype.card F : ℝ) ^ ((((2 * r - i) * i : ℕ)) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hexp]; nlinarith
      _ = ((Fintype.card F ^ ((2 * r - i) * i) : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := by exact_mod_cast hlo
  · calc (Nat.card {U : Submodule F (Fin (2 * r) → F) // finrank F U = i} : ℝ)
        ≤ ((2 ^ i * Fintype.card F ^ ((2 * r - i) * i) : ℕ) : ℝ) := by exact_mod_cast hup
      _ ≤ (((Fintype.card F ^ (i + (2 * r - i) * i)) : ℕ) : ℝ) := by
          rw [pow_add]
          have : 2 ^ i ≤ Fintype.card F ^ i := Nat.pow_le_pow_left (q_two_le) i
          exact_mod_cast Nat.mul_le_mul_right _ this
      _ = (Fintype.card F : ℝ) ^ (((i + (2 * r - i) * i : ℕ)) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          have : (((i + (2 * r - i) * i : ℕ)) : ℝ) = i + ((r : ℝ) ^ 2 - ((r : ℝ) - i) ^ 2) := by
            rw [Nat.cast_add, hexp]
          rw [this]
          nlinarith [sq_nonneg ((r : ℝ) - i)]

theorem vertices_subset [DecidableEq (Submodule F (Fin (2 * r) → F))] (hr : 1 ≤ r) :
    faces (flagsComplex F r k) 1 ⊆ (Finset.Icc (r - k) (r + k)).biUnion (fun i =>
      (faces (flagsComplex F r k) 1).filter
        (fun s => ∀ W ∈ s, finrank F (W : Submodule F (Fin (2 * r) → F)) = i)) := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
  obtain ⟨W, rfl⟩ := Finset.card_eq_one.1 hs2
  refine Finset.mem_biUnion.2 ⟨finrank F W, ?_, Finset.mem_filter.2 ⟨hs, ?_⟩⟩
  · exact Finset.mem_Icc.2 ((mem_flagsComplex.1 hs1).1 W (Finset.mem_singleton_self W))
  · intro W' hW'; rw [Finset.mem_singleton.1 hW']

end Complex

theorem flags_counts : ∃ c₀ c₁ c₂ C : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ (F : Type*) [Field F] [Fintype F] (r k : ℕ)
      [DecidableEq (Submodule F (Fin (2 * r) → F))], 1 ≤ k → k < r →
      (∀ i ∈ Finset.Icc (r - k) (r + k),
        (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - c₀ * k * r) ≤
          (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ∧
        (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ≤
          (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + c₀ * k * r)) ∧
      (Fintype.card F : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces (flagsComplex F r k) 1).card : ℝ) ∧
      ((faces (flagsComplex F r k) 1).card : ℝ) ≤ (Fintype.card F : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree (flagsComplex F r k) (2 * k + 1) : ℝ) ≤
        (Fintype.card F : ℝ) ^ (C * k * r) := by
  refine ⟨2, 1, 6, 6, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro F _ _ r k _ hk1 hk
  have hQ2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast q_two_le (F := F)
  have hQ1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by linarith
  have hrk : (k : ℝ) < r := by exact_mod_cast hk
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hr1 : 1 ≤ r := by omega
  have hvb : ∀ i ∈ Finset.Icc (r - k) (r + k),
      (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - 2 * k * r) ≤
          (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ∧
        (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ≤
          (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + 2 * k * r) := by
    intro i hi
    rw [card_vertices_dim (F := F) (r := r) (k := k) i (Finset.mem_Icc.1 hi)]
    exact vertex_bounds (F := F) hk1 hk i (Finset.mem_Icc.1 hi)
  refine ⟨hvb, ?_, ?_, ?_⟩
  · -- lower bound on the number of vertices
    have hr : r ∈ Finset.Icc (r - k) (r + k) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hfr : finrank F (Fin (2 * r) → F) = 2 * r := by simp
    obtain ⟨hlo, _⟩ := gauss_bounds (F := F) (V := Fin (2 * r) → F) r (by rw [hfr]; omega)
    rw [hfr] at hlo
    have h1 : (Fintype.card F ^ ((2 * r - r) * r) : ℕ) ≤
        (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = r)).card) := by
      rw [card_vertices_dim (F := F) (r := r) (k := k) r (Finset.mem_Icc.1 hr)]; exact hlo
    have h2 := (Finset.card_le_card (Finset.filter_subset
      (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = r)
      (faces (flagsComplex F r k) 1)))
    have h3 : (Fintype.card F ^ ((2 * r - r) * r) : ℕ) ≤ (faces (flagsComplex F r k) 1).card :=
      h1.trans h2
    calc (Fintype.card F : ℝ) ^ (1 * (r : ℝ) ^ 2)
        = ((Fintype.card F ^ ((2 * r - r) * r) : ℕ) : ℝ) := by
          have : 1 * (r : ℝ) ^ 2 = (((2 * r - r) * r : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
          rw [this, Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := by exact_mod_cast h3
  · -- upper bound on the number of vertices
    have hsum := (Finset.card_le_card (vertices_subset (F := F) (k := k) hr1)).trans
      Finset.card_biUnion_le
    have hsumR : ((faces (flagsComplex F r k) 1).card : ℝ) ≤
        ∑ i ∈ Finset.Icc (r - k) (r + k), ((((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have hle : ∑ i ∈ Finset.Icc (r - k) (r + k), ((((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℕ) : ℝ)
        ≤ ∑ _i ∈ Finset.Icc (r - k) (r + k), (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + 2 * k * r) :=
      Finset.sum_le_sum (fun i hi => (hvb i hi).2)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hle
    have hcnt : r + k + 1 - (r - k) = 2 * k + 1 := by omega
    rw [hcnt] at hle
    have hpow : ((2 * k + 1 : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) ^ ((2 * k + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      have h1 : 2 * k + 1 < 2 ^ (2 * k + 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (2 * k + 1) ≤ Fintype.card F ^ (2 * k + 1) :=
        Nat.pow_le_pow_left (q_two_le) _
      exact_mod_cast (h1.trans_le h2).le
    calc ((faces (flagsComplex F r k) 1).card : ℝ)
        ≤ ((2 * k + 1 : ℕ) : ℝ) * (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + 2 * k * r) :=
          hsumR.trans hle
      _ ≤ (Fintype.card F : ℝ) ^ ((2 * k + 1 : ℕ) : ℝ) *
            (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + 2 * k * r) := by
          exact mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (Fintype.card F : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) + ((r : ℝ) ^ 2 + 2 * k * r)) := by
          exact (Real.rpow_add (by linarith) _ _).symm
      _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          push_cast
          nlinarith
  · -- degree
    have hd := degree_le (F := F) (r := r) (k := k) hk
    have hdR : (degree (flagsComplex F r k) (2 * k + 1) : ℝ) ≤
        ((Fintype.card F ^ (2 * r * (2 * k + 1)) : ℕ) : ℝ) := by
      rw [pow_mul]; exact_mod_cast hd
    refine hdR.trans ?_
    have hc : ((Fintype.card F ^ (2 * r * (2 * k + 1)) : ℕ) : ℝ) =
        (Fintype.card F : ℝ) ^ (((2 * r * (2 * k + 1) : ℕ)) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; rfl
    rw [hc]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    push_cast
    nlinarith

end SteurerHDX.Dev.Flags3
end

section
namespace SteurerHDX

theorem chk_section_2_3_flags :
    ∃ c₀ c₁ c₂ C : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ (F : Type*) [Field F] [Fintype F] (r k : ℕ)
      [DecidableEq (Submodule F (Fin (2 * r) → F))], 1 ≤ k → k < r →
      IsPure (flagsComplex F r k) (2 * k + 1) ∧
      IsPartite (flagsComplex F r k) (2 * k + 1) ∧
      (∀ σ, σ ∈ faces (flagsComplex F r k) (2 * k + 1) ↔
        σ ∈ flagsComplex F r k ∧
          σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) = Finset.Icc (r - k) (r + k)) ∧
      (∀ i ∈ Finset.Icc (r - k) (r + k),
        (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - c₀ * k * r) ≤
          (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ∧
        (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ≤
          (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + c₀ * k * r)) ∧
      (Fintype.card F : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces (flagsComplex F r k) 1).card : ℝ) ∧
      ((faces (flagsComplex F r k) 1).card : ℝ) ≤ (Fintype.card F : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree (flagsComplex F r k) (2 * k + 1) : ℝ) ≤
        (Fintype.card F : ℝ) ^ (C * k * r) ∧
      IsTopLinkExpander (flagsComplex F r k) (2 * k + 1)
        (2 / (Real.sqrt (Fintype.card F) - 1)) := by
  obtain ⟨c₀, c₁, c₂, C, h0, h1, h2, h3, h⟩ := Dev.Flags3.flags_counts
  refine ⟨c₀, c₁, c₂, C, h0, h1, h2, h3, ?_⟩
  intro F _ _ r k _ hk hkr
  obtain ⟨ha, hb, hc, hd⟩ := h F r k hk hkr
  exact ⟨Dev.Flags2.flags_pure F r k hk hkr, Dev.Flags2.flags_partite F r k hk hkr,
    Dev.Flags2.flags_faces F r k hk hkr, ha, hb, hc, hd, Dev.Flags.flags_topLink F r k hk hkr⟩

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_section_2_3_flags := @SteurerHDX.chk_section_2_3_flags
