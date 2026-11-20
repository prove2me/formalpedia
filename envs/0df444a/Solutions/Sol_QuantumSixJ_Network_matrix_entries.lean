-- Prove2me | solution 1 for QuantumSixJ.Network.matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T18:58:33.352286+00:00
-- url     : https://prove2.me/submissions/1cb50144-3bbb-44a5-a026-6fc88d2a6061

import Definitions.Def_QuantumSixJNetwork
import Theorems.Thm_QuantumSixJ_scalar_foundations
import Theorems.Thm_QuantumSixJ_tet_two_evaluations
import Theorems.Thm_QuantumSixJ_Network_diagram_calculus
import Theorems.Thm_QuantumSixJ_Network_four_valent_bases

open CategoryTheory MonoidalCategory
universe v u
noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

namespace QuantumSixJ.Network

set_option maxRecDepth 8192

/-- The two nested mates of a rotated covector agree after closing them, since
three rotations of a vertex are the identity by cyclicity. -/
private lemma matrix_rotate_mates {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C)
    (h3 : Vertex.rotate (Vertex.rotate (Vertex.rotate f)) = f) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b))
      ((tensorLeftHomEquiv
        (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    (tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a))
      ((tensorRightHomEquiv
        (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C))
        ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
          (λ_ (S.V a)).hom) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let close (h : S.V l ⟶ S.V a ⊗ S.V b) :
      S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V l) (S.V b) (S.V a)).inv ≫
      eRa.symm (eRb.symm h ≫ (λ_ (S.V a)).inv)
  have close_injective : Function.Injective close := by
    intro x y hxy
    apply eRb.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply eRa.symm.injective
    rw [← cancel_epi (α_ (S.V l) (S.V b) (S.V a)).inv]
    exact hxy
  have close_right :
      close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)) = f := by
    simp only [close, Equiv.symm_apply_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have close_left_rotate3 :
      close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := by
    simp [close, eLa, eLb, eRa, eRb, tensorLeftHomEquiv, tensorRightHomEquiv,
      Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, monoidalComp]
    monoidal
  change eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫ (λ_ (S.V a)).hom)
  apply close_injective
  calc
    close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := close_left_rotate3
    _ = f := h3
    _ = close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
      (λ_ (S.V a)).hom)) := close_right.symm

/-- Bend a cup through a split vertex. -/
private lemma matrix_cup_split {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b l : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V a ⊗ S.V b)
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let r : S.V l ⟶ S.V a ⊗ S.V b :=
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ W.vertex l b a) ≫
      (λ_ (S.V a)).hom)
  have hsplit : W.split l a b =
      eLa (eLb (W.vertex b a l) ≫ (ρ_ (S.V b)).hom) := by
    dsimp [eLa, eLb, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hup : W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv =
      e ((λ_ (S.V l)).hom ≫ r) := by
    dsimp [e, r, eRa, eRb, tensorRightHomEquiv]
    simp only [Vertex.vertexUp, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hrot3 : Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex l b a))) =
      W.vertex l b a := by
    rw [hW.cyclic l b a, hW.cyclic b a l, hW.cyclic a l b]
  have hm : W.split l a b = r := by
    rw [hsplit, ← hW.cyclic l b a]
    exact matrix_rotate_mates S a b l (W.vertex l b a) hrot3
  calc
    S.cup l ≫ (W.split l a b ▷ S.V l) =
        e ((λ_ (S.V l)).hom ≫ W.split l a b) := by
      simp [e, tensorRightHomEquiv, SuQ2Data.cup,
        ExactPairing.coevaluation, comp_whiskerRight, unitors_equal]
    _ = e ((λ_ (S.V l)).hom ≫ r) := by rw [hm]
    _ = W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := hup.symm

private lemma matrix_iota_ne_zero (r : Scalar) (hr : r ≠ 0) : ι r ≠ 0 := by
  apply (map_ne_zero_iff _ _).2 hr
  unfold ι
  apply RatFunc.map_injective
  · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

private lemma matrix_unit_injective {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) :
    Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)) := by
  intro r s hrs
  have hrs0 : r • 𝟙 (S.V 0) = s • 𝟙 (S.V 0) := by
    have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => S.unitIso.hom ≫ f ≫ S.unitIso.inv) hrs
    simpa [smul_smul] using h
  have hd : (0 : S.V 0 ⟶ S.V 0) = (r - s) • 𝟙 (S.V 0) := by
    rw [sub_smul, hrs0, sub_self]
  have hz : (0 : S.V 0 ⟶ S.V 0) = (0 : K) • 𝟙 (S.V 0) := by simp
  exact sub_eq_zero.mp ((hS.simple 0 0).unique hd hz)

private lemma matrix_fuse_cap {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) :
    (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let f := (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l
  have hfuse : W.fuse a b l =
      (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)) f ≫
        (λ_ (S.V l)).hom := by
    simp [f, Vertex.fuse, tensorRightHomEquiv, monoidalComp,
      SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
      ExactPairing.evaluation]
  rw [hfuse]
  simpa [f, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal] using
    (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)).left_inv f

private lemma matrix_closed_assembly {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ)
    (hcup : S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (hfuse : (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l) :
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      W.vertexUp a b l ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l), hcup]
  simp only [Category.assoc]
  rw [hfuse]
  simp

private lemma matrix_bubble_from_closed {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (a b l : ℕ) (u : K)
    (hclosed : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      u • 𝟙 (𝟙_ C)) :
    W.split l a b ≫ W.fuse a b l = (u / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  obtain ⟨s, hs, _⟩ := hS.simple l (W.split l a b ≫ W.fuse a b l)
  have hclosed' : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      (s * ι (Δ (l : ℤ))) • 𝟙 (𝟙_ C) := by
    rw [hs]
    simp [hS.loop, smul_smul]
  have hscalar : s * ι (Δ (l : ℤ)) = u := by
    apply matrix_unit_injective S hS
    exact hclosed'.symm.trans hclosed
  have hΔ : ι (Δ (l : ℤ)) ≠ 0 := matrix_iota_ne_zero _ (delta_ne_zero l (by omega))
  have hsval : s = u / ι (Δ (l : ℤ)) := (eq_div_iff hΔ).2 hscalar
  rw [← hsval]
  exact hs

private lemma matrix_bubble {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ) :
    W.split l a b ≫ W.fuse a b l =
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  apply matrix_bubble_from_closed S W hS a b l (ι (θ (a : ℤ) b l))
  calc
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        W.vertexUp a b l ≫ W.vertex a b l :=
      matrix_closed_assembly S W a b l (matrix_cup_split S W hW a b l)
        (matrix_fuse_cap S W a b l)
    _ = ι (θ (a : ℤ) b l) • 𝟙 (𝟙_ C) := hW.theta a b l

private lemma matrix_fusion_left_scalar {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hi : ∀ n ∈ fusionRange a b, i n ≫ p n = 𝟙 (S.V n))
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∈ fusionRange a b) (f : S.V l ⟶ S.V a ⊗ S.V b) :
    ∃ t : K, f = t • i l := by
  have hf : f = ∑ n ∈ fusionRange a b, (f ≫ p n) ≫ i n := by
    calc
      f = f ≫ 𝟙 (S.V a ⊗ S.V b) := by simp
      _ = f ≫ ∑ n ∈ fusionRange a b, p n ≫ i n := by rw [hpi]
      _ = ∑ n ∈ fusionRange a b, (f ≫ p n) ≫ i n := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Category.assoc]
  obtain ⟨t, ht, _⟩ := hS.simple l (f ≫ p l)
  refine ⟨t, ?_⟩
  rw [hf, Finset.sum_eq_single l]
  · rw [ht]
    simp
  · intro n hn hnl
    have hzero : f ≫ p n = 0 := hS.disjoint l n (Ne.symm hnl) _
    simp [hzero]
  · exact fun h => (h hl).elim

private lemma matrix_fusion_right_scalar {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hi : ∀ n ∈ fusionRange a b, i n ≫ p n = 𝟙 (S.V n))
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∈ fusionRange a b) (f : S.V a ⊗ S.V b ⟶ S.V l) :
    ∃ t : K, f = t • p l := by
  have hf : f = ∑ n ∈ fusionRange a b, p n ≫ (i n ≫ f) := by
    calc
      f = 𝟙 (S.V a ⊗ S.V b) ≫ f := by simp
      _ = (∑ n ∈ fusionRange a b, p n ≫ i n) ≫ f := by rw [hpi]
      _ = ∑ n ∈ fusionRange a b, p n ≫ (i n ≫ f) := by
        rw [Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Category.assoc]
  obtain ⟨t, ht, _⟩ := hS.simple l (i l ≫ f)
  refine ⟨t, ?_⟩
  rw [hf, Finset.sum_eq_single l]
  · rw [ht]
    simp
  · intro n hn hnl
    have hzero : i n ≫ f = 0 := hS.disjoint n l hnl _
    simp [hzero]
  · exact fun h => (h hl).elim

private lemma matrix_resolution {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b : ℕ) :
    ∑ l ∈ fusionRange a b,
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ •
        (W.fuse a b l ≫ W.split l a b) = 𝟙 (S.V a ⊗ S.V b) := by
  obtain ⟨i, p, hi, hpi⟩ := hS.fusion a b
  calc
    (∑ l ∈ fusionRange a b,
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ •
        (W.fuse a b l ≫ W.split l a b)) = ∑ l ∈ fusionRange a b, p l ≫ i l := by
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨u, hu⟩ := matrix_fusion_left_scalar S hS a b l i p hi hpi hl
        (W.split l a b)
      obtain ⟨w, hw⟩ := matrix_fusion_right_scalar S hS a b l i p hi hpi hl
        (W.fuse a b l)
      have huw : u * w = ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)) := by
        apply (hS.simple l (W.split l a b ≫ W.fuse a b l)).unique
        · rw [hu, hw, Linear.smul_comp, Linear.comp_smul, hi l hl]
          simp [smul_smul]
        · exact matrix_bubble S W hS hW a b l
      rw [hu, hw]
      simp only [Linear.comp_smul, Linear.smul_comp, smul_smul]
      have hr : ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)) ≠ 0 := by
        apply div_ne_zero
        · exact matrix_iota_ne_zero _ (theta_ne_zero _ _ _ (Finset.mem_filter.mp hl).2)
        · exact matrix_iota_ne_zero _ (delta_ne_zero l (by omega))
      have hcoef : (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ * (u * w) = 1 := by
        rw [huw]
        exact inv_mul_cancel₀ hr
      rw [hcoef, one_smul]
    _ = 𝟙 (S.V a ⊗ S.V b) := hpi

private lemma matrix_pair_state_ne {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (k l : ℕ) (hkl : k ≠ l)
    (q : 𝟙_ C ⟶ S.V k ⊗ S.V l) : q = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V k)
  have hF : (λ_ (S.V l)).inv ≫ e.symm q = 0 := hS.disjoint l k (Ne.symm hkl) _
  have he : e.symm q = 0 := by
    calc
      e.symm q = (λ_ (S.V l)).hom ≫ (λ_ (S.V l)).inv ≫ e.symm q := by simp
      _ = 0 := by rw [hF]; simp
  calc
    q = e (e.symm q) := (e.right_inv q).symm
    _ = 0 := by rw [he]; simp [e, tensorRightHomEquiv]

private lemma matrix_pair_state_eq {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (l : ℕ)
    (q : 𝟙_ C ⟶ S.V l ⊗ S.V l) : ∃ t : K, q = t • S.cup l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V l)
  let F : S.V l ⟶ S.V l := (λ_ (S.V l)).inv ≫ e.symm q
  obtain ⟨t, ht, _⟩ := hS.simple l F
  have hq : q = e ((λ_ (S.V l)).hom ≫ F) := by
    calc
      q = e (e.symm q) := (e.right_inv q).symm
      _ = e ((λ_ (S.V l)).hom ≫ F) := by simp [F]
  have hcup : e (λ_ (S.V l)).hom = S.cup l := by
    simp [e, tensorRightHomEquiv, SuQ2Data.cup, ExactPairing.coevaluation,
      ← unitors_equal]
    monoidal
  refine ⟨t, ?_⟩
  calc
    q = e ((λ_ (S.V l)).hom ≫ F) := hq
    _ = e (t • (λ_ (S.V l)).hom) := by rw [ht]; simp
    _ = t • e (λ_ (S.V l)).hom := by
      dsimp [e, tensorRightHomEquiv]
      simp
    _ = t • S.cup l := by rw [hcup]

private lemma matrix_pair_covector_ne {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (k l : ℕ) (hkl : k ≠ l)
    (q : S.V k ⊗ S.V l ⟶ 𝟙_ C) : q = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (S.V k) (S.V l) (S.V l) (𝟙_ C)
  have hF : e q ≫ (λ_ (S.V l)).hom = 0 := hS.disjoint k l hkl _
  have he : e q = 0 := by
    calc
      e q = e q ≫ (λ_ (S.V l)).hom ≫ (λ_ (S.V l)).inv := by simp
      _ = 0 := by rw [← Category.assoc, hF]; simp
  calc
    q = e.symm (e q) := (e.left_inv q).symm
    _ = 0 := by rw [he]; simp [e, tensorRightHomEquiv]

private lemma matrix_pair_covector_eq {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (l : ℕ)
    (q : S.V l ⊗ S.V l ⟶ 𝟙_ C) : ∃ t : K, q = t • S.cap l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (S.V l) (S.V l) (S.V l) (𝟙_ C)
  let F : S.V l ⟶ S.V l := e q ≫ (λ_ (S.V l)).hom
  obtain ⟨t, ht, _⟩ := hS.simple l F
  refine ⟨t, ?_⟩
  have hcap : e (S.cap l) = (λ_ (S.V l)).inv := by
    dsimp [e, tensorRightHomEquiv]
    change (ρ_ (S.V l)).inv ≫ S.V l ◁ η_ (S.V l) (S.V l) ≫
      (α_ (S.V l) (S.V l) (S.V l)).inv ≫ ε_ (S.V l) (S.V l) ▷ S.V l =
        (λ_ (S.V l)).inv
    rw [ExactPairing.coevaluation_evaluation]
    simp
  have heq0 : e q = t • (λ_ (S.V l)).inv := by
    calc
      e q = (e q ≫ (λ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv := by simp
      _ = (t • 𝟙 (S.V l)) ≫ (λ_ (S.V l)).inv := by rw [← ht]
      _ = t • (λ_ (S.V l)).inv := by simp
  have heq : e q = t • e (S.cap l) := by rw [hcap, heq0]
  have hsymm (z : S.V l ⟶ 𝟙_ C ⊗ S.V l) : e.symm (t • z) = t • e.symm z := by
    dsimp [e, tensorRightHomEquiv]
    simp
  calc
    q = e.symm (e q) := (e.left_inv q).symm
    _ = e.symm (t • e (S.cap l)) := by rw [heq]
    _ = t • e.symm (e (S.cap l)) := hsymm _
    _ = t • S.cap l := by
      congr 1
      exact e.left_inv _

private lemma matrix_triple_state {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) (r : ℕ → K)
    (hres : ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ W.split k a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hcup : S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V l)
    (hpair_ne : ∀ k : ℕ, k ≠ l → ∀ z : 𝟙_ C ⟶ S.V k ⊗ S.V l, z = 0)
    (hpair_eq : ∀ z : 𝟙_ C ⟶ S.V l ⊗ S.V l, ∃ t : K, z = t • S.cup l) :
    ∃ t : K, q = t • W.vertexUp a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let Q (k : ℕ) : 𝟙_ C ⟶ S.V k ⊗ S.V l :=
    q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫ (W.fuse a b k ▷ S.V l)
  have hq : q = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
      (Q k ≫ (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom) := by
    calc
      q = q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom := by simp
      _ = q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          ((∑ k ∈ fusionRange a b, (r k)⁻¹ •
            (W.fuse a b k ≫ W.split k a b)) ▷ S.V l) ≫
            (α_ (S.V a) (S.V b) (S.V l)).hom := by rw [hres]
      _ = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
          (Q k ≫ (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom) := by
        simp [Q, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  by_cases hl : l ∈ fusionRange a b
  · obtain ⟨t, ht⟩ := hpair_eq (Q l)
    refine ⟨t * (r l)⁻¹, ?_⟩
    rw [hq, Finset.sum_eq_single l]
    · dsimp [Q] at ht ⊢
      rw [ht]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [← Category.assoc (S.cup l), hcup]
      simp [smul_smul]
      ring
    · intro k hk hkl
      rw [hpair_ne k hkl (Q k)]
      simp
    · exact fun h => (h hl).elim
  · refine ⟨0, ?_⟩
    rw [hq]
    simp only [zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkl : k ≠ l := by
      intro h
      subst k
      exact hl hk
    rw [hpair_ne k hkl (Q k)]
    simp

private lemma matrix_triple_covector {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) (r : ℕ → K)
    (hres : ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ W.split k a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hcap : (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l)
    (q : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C)
    (hpair_ne : ∀ k : ℕ, k ≠ l → ∀ z : S.V k ⊗ S.V l ⟶ 𝟙_ C, z = 0)
    (hpair_eq : ∀ z : S.V l ⊗ S.V l ⟶ 𝟙_ C, ∃ t : K, z = t • S.cap l) :
    ∃ t : K, q = t • W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let Q (k : ℕ) : S.V k ⊗ S.V l ⟶ 𝟙_ C :=
    (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q
  have hq : q = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
      ((α_ (S.V a) (S.V b) (S.V l)).inv ≫
        (W.fuse a b k ▷ S.V l) ≫ Q k) := by
    calc
      q = (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ S.V l) ≫
          (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q := by simp
      _ = (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          ((∑ k ∈ fusionRange a b, (r k)⁻¹ •
            (W.fuse a b k ≫ W.split k a b)) ▷ S.V l) ≫
          (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q := by rw [hres]
      _ = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
          ((α_ (S.V a) (S.V b) (S.V l)).inv ≫
            (W.fuse a b k ▷ S.V l) ≫ Q k) := by
        simp [Q, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  by_cases hl : l ∈ fusionRange a b
  · obtain ⟨t, ht⟩ := hpair_eq (Q l)
    refine ⟨t * (r l)⁻¹, ?_⟩
    rw [hq, Finset.sum_eq_single l]
    · dsimp [Q] at ht ⊢
      rw [ht]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [hcap]
      simp [smul_smul]
      ring
    · intro k hk hkl
      rw [hpair_ne k hkl (Q k)]
      simp
    · exact fun h => (h hl).elim
  · refine ⟨0, ?_⟩
    rw [hq]
    simp only [zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkl : k ≠ l := by
      intro h
      subst k
      exact hl hk
    rw [hpair_ne k hkl (Q k)]
    simp

private lemma matrix_any_triple_state {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ)
    (q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V l) :
    ∃ t : K, q = t • W.vertexUp a b l :=
  matrix_triple_state S W a b l
    (fun k => ι (θ (a : ℤ) b k) / ι (Δ (k : ℤ)))
    (matrix_resolution S W hS hW a b) (matrix_cup_split S W hW a b l) q
    (fun k hkl z => matrix_pair_state_ne S hS k l hkl z)
    (matrix_pair_state_eq S hS l)

private lemma matrix_any_triple_covector {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ)
    (q : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    ∃ t : K, q = t • W.vertex a b l :=
  matrix_triple_covector S W a b l
    (fun k => ι (θ (a : ℤ) b k) / ι (Δ (k : ℤ)))
    (matrix_resolution S W hS hW a b) (matrix_fuse_cap S W a b l) q
    (fun k hkl z => matrix_pair_covector_ne S hS k l hkl z)
    (matrix_pair_covector_eq S hS l)

/-- Channel scalarity in the directly oriented, rather than covector-mated,
form. This is the form used by the inner rung network. -/
private lemma matrix_any_fuse_scalar {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ) (q : S.V a ⊗ S.V b ⟶ S.V l) :
    ∃ t : K, q = t • W.fuse a b l := by
  let r : ℕ → K := fun k => ι (θ (a : ℤ) b k) / ι (Δ (k : ℤ))
  have hres := matrix_resolution S W hS hW a b
  let Q (k : ℕ) : S.V k ⟶ S.V l := W.split k a b ≫ q
  have hq : q = ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ Q k) := by
    calc
      q = 𝟙 (S.V a ⊗ S.V b) ≫ q := by simp
      _ = (∑ k ∈ fusionRange a b, (r k)⁻¹ •
          (W.fuse a b k ≫ W.split k a b)) ≫ q := by rw [hres]
      _ = ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ Q k) := by
        simp [Q, r, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  by_cases hl : l ∈ fusionRange a b
  · obtain ⟨t, ht, _⟩ := hS.simple l (Q l)
    refine ⟨t * (r l)⁻¹, ?_⟩
    rw [hq, Finset.sum_eq_single l]
    · dsimp [Q] at ht ⊢
      rw [ht]
      simp [Linear.comp_smul, Linear.smul_comp, smul_smul]
      ring
    · intro k hk hkl
      have hz : Q k = 0 := hS.disjoint k l hkl _
      simp [hz]
    · exact fun h => (h hl).elim
  · refine ⟨0, ?_⟩
    rw [hq]
    simp only [zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkl : k ≠ l := by
      intro h
      subst k
      exact hl hk
    have hz : Q k = 0 := hS.disjoint k l hkl _
    simp [hz]

/-- The vertex-collapse identity for an arbitrary three-strand factorization.
The two factors on the left are the closures of the state and covector by the
canonical trivalent vertex. -/
private lemma matrix_vertex_collapse {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ)
    (Q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V l)
    (R : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    (Q ≫ W.vertex a b l) ≫ (W.vertexUp a b l ≫ R) =
      ι (θ (a : ℤ) b l) • (Q ≫ R) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  obtain ⟨t, ht⟩ := matrix_any_triple_state S W hS hW a b l Q
  obtain ⟨u, hu⟩ := matrix_any_triple_covector S W hS hW a b l R
  have hq : Q ≫ W.vertex a b l = (t * ι (θ (a : ℤ) b l)) • 𝟙 (𝟙_ C) := by
    rw [ht]
    simp [Linear.smul_comp, hW.theta, smul_smul]
  have hr : W.vertexUp a b l ≫ R = (u * ι (θ (a : ℤ) b l)) • 𝟙 (𝟙_ C) := by
    rw [hu]
    simp [Linear.comp_smul, hW.theta, smul_smul]
  have hqr : Q ≫ R = (t * u * ι (θ (a : ℤ) b l)) • 𝟙 (𝟙_ C) := by
    rw [ht, hu]
    simp [Linear.smul_comp, Linear.comp_smul, hW.theta, smul_smul]
    ring
  rw [hq, hr, hqr]
  simp [smul_smul]
  ring
namespace MatrixTriangle

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
  (S : SuQ2Data C) (W : Vertex S)

/-- The right three-vertex triangle, open on strands 2,j',j. -/
noncomputable def right (b c j j' : ℕ) : S.V 2 ⊗ S.V j' ⟶ S.V j :=
  (S.V 2 ◁ W.split j' b c) ⊗≫
    (W.fuse 2 b b ▷ S.V c) ≫ W.fuse b c j

/-- Close an arbitrary right triangle against the left three-vertex triangle. -/
noncomputable def leftClose (a d j j' : ℕ)
    (q : S.V 2 ⊗ S.V j' ⟶ S.V j) : 𝟙_ C ⟶ 𝟙_ C :=
  W.vertexUp a j' d ⊗≫ (W.split a a 2 ▷ (S.V j' ⊗ S.V d)) ⊗≫
    (S.V a ◁ (q ▷ S.V d)) ⊗≫ W.vertex a j d

/-- Literal left four-vertex tetrahedral closure, with the canonical fuse. -/
noncomputable def leftTet (a d j j' : ℕ) : 𝟙_ C ⟶ 𝟙_ C :=
  leftClose S W a d j j' (W.fuse 2 j' j)

/-- Literal right four-vertex tetrahedral closure: trace after splitting j. -/
noncomputable def rightTet (b c j j' : ℕ) : 𝟙_ C ⟶ 𝟙_ C :=
  S.cup j ≫ ((W.split j 2 j' ≫ right S W b c j j') ▷ S.V j) ≫ S.cap j

lemma entry_as_triangle (a b c d j j' : ℕ) :
    W.H a b c d j' ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) •
        leftClose S W a d j j' (right S W b c j j') := by
  have hx := MonoidalCategory.whisker_exchange (W.split a a 2) (W.split j' b c)
  have h := congrArg
    (fun z : S.V a ⊗ S.V j' ⟶ (S.V a ⊗ S.V 2) ⊗ (S.V b ⊗ S.V c) =>
      W.vertexUp a j' d ⊗≫ (z ▷ S.V d) ⊗≫
        ((S.V a ◁ (W.fuse 2 b b ▷ S.V c)) ▷ S.V d) ⊗≫
          (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ W.vertex a j d) hx
  have hg : (W.H a b c d j' ≫
      (𝟙 _ ⊗≫
        (((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)) ▷
          (S.V c ⊗ S.V d)) ⊗≫ 𝟙 _) ≫ W.Hcov a b c d j) =
        leftClose S W a d j j' (right S W b c j j') := by
    simp [Vertex.H, Vertex.Hcov, right, leftClose, monoidalComp] at h ⊢
    convert h using 1 <;> monoidal
  simpa [Vertex.Kop, Vertex.K2, monoidalComp, smul_smul] using
    congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) • f) hg

lemma right_zero_of_inadmissible (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (b c j j' : ℕ) (ha : ¬ Admissible (2 : ℤ) j' j) : right S W b c j j' = 0 := by
  have hres := matrix_resolution S W hS hW 2 j'
  norm_num only [Nat.cast_ofNat] at hres
  have hq : right S W b c j j' = ∑ k ∈ fusionRange 2 j',
      (ι (θ (2 : ℤ) j' k) / ι (Δ (k : ℤ)))⁻¹ •
        (W.fuse 2 j' k ≫ (W.split k 2 j' ≫ right S W b c j j')) := by
    calc
      right S W b c j j' = 𝟙 (S.V 2 ⊗ S.V j') ≫ right S W b c j j' := by simp
      _ = (∑ k ∈ fusionRange 2 j',
          (ι (θ (2 : ℤ) j' k) / ι (Δ (k : ℤ)))⁻¹ •
            (W.fuse 2 j' k ≫ W.split k 2 j')) ≫ right S W b c j j' := by rw [hres]
      _ = _ := by simp [Preadditive.sum_comp, Category.assoc]
  rw [hq]
  apply Finset.sum_eq_zero
  intro k hk
  have hkj : k ≠ j := by
    intro heq
    subst k
    exact ha (Finset.mem_filter.mp hk).2
  have hz := hS.disjoint k j hkj (W.split k 2 j' ≫ right S W b c j j')
  rw [hz]
  simp

lemma canonical_trace (hW : VertexNormalized W) (j j' : ℕ) :
    S.cup j ≫ ((W.split j 2 j' ≫ W.fuse 2 j' j) ▷ S.V j) ≫ S.cap j =
      ι (θ (2 : ℤ) j' j) • 𝟙 (𝟙_ C) := by
  rw [matrix_closed_assembly S W 2 j' j
    (matrix_cup_split S W hW 2 j' j) (matrix_fuse_cap S W 2 j' j)]
  exact hW.theta 2 j' j

/-- Exact factorization into the literal tetrahedral closures produced by the
triangle calculation. The central-theta zero case is included, not assumed. -/
theorem factorization (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b c d j j' : ℕ) :
    W.H a b c d j' ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      (ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) / ι (θ (2 : ℤ) j' j)) •
        (leftTet S W a d j j' ≫ rightTet S W b c j j') := by
  rw [entry_as_triangle S W]
  by_cases ha : Admissible (2 : ℤ) j' j
  · obtain ⟨s, hs⟩ := matrix_any_fuse_scalar S W hS hW 2 j' j (right S W b c j j')
    have hn : ι (θ (2 : ℤ) j' j) ≠ 0 :=
      matrix_iota_ne_zero _ (theta_ne_zero _ _ _ ha)
    have ht : rightTet S W b c j j' = (s * ι (θ (2 : ℤ) j' j)) • 𝟙 (𝟙_ C) := by
      calc
        rightTet S W b c j j' = s •
            (S.cup j ≫ ((W.split j 2 j' ≫ W.fuse 2 j' j) ▷ S.V j) ≫ S.cap j) := by
          simp [rightTet, hs]
        _ = _ := by rw [canonical_trace S W hW]; simp [smul_smul]
    have hc : leftClose S W a d j j' (right S W b c j j') =
        s • leftTet S W a d j j' := by
      rw [hs]
      simp [leftClose, leftTet, monoidalComp]
    rw [hc, ht]
    simp only [Linear.comp_smul, Category.comp_id, smul_smul]
    congr 1
    field_simp [hn]
    <;> ring
  · have hz := right_zero_of_inadmissible S W hS hW b c j j' ha
    simp [rightTet, hz, leftClose, monoidalComp]

/-- Inadmissibility of the central channel forces the original matrix entry
to vanish, independently of division by theta. -/
theorem entry_zero (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b c d j j' : ℕ) (ha : ¬ Admissible (2 : ℤ) j' j) :
    W.H a b c d j' ≫ W.Kop a b c d ≫ W.Hcov a b c d j = 0 := by
  rw [entry_as_triangle S W, right_zero_of_inadmissible S W hS hW b c j j' ha]
  simp [leftClose, monoidalComp]

/-- Tridiagonality, with the parity restriction included. -/
theorem sparse (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b c d j j' : ℕ) (hne : j' ≠ j) (hp : j' ≠ j + 2) (hm : j ≠ j' + 2) :
    W.H a b c d j' ≫ W.Kop a b c d ≫ W.Hcov a b c d j = 0 := by
  apply entry_zero S W hS hW
  intro ha
  rcases ha with ⟨h2, hj', hj, ht1, ht2, ht3, hpar⟩
  omega

/-- The exceptional zero diagonal entry is included in the graphical proof. -/
theorem zero_diagonal (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b c d : ℕ) : W.H a b c d 0 ≫ W.Kop a b c d ≫ W.Hcov a b c d 0 = 0 := by
  apply entry_zero S W hS hW
  norm_num [Admissible]

end
end MatrixTriangle
private def rungSplit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (S : SuQ2Data C) {a b l : ℕ}
    (f : S.V b ⊗ S.V a ⊗ S.V l ⟶ 𝟙_ C) : S.V l ⟶ S.V a ⊗ S.V b :=
  𝟙 _ ⊗≫ (S.cup a ▷ S.V l) ⊗≫
    (S.V a ◁ ((S.cup b ▷ S.V a) ▷ S.V l)) ⊗≫
    (S.V a ◁ S.V b ◁ f) ⊗≫ 𝟙 _

/-- Fusing two strands by an otherwise arbitrary covector. -/
private def rungFuse {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (S : SuQ2Data C) {a b l : ℕ}
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) : S.V a ⊗ S.V b ⟶ S.V l :=
  𝟙 _ ⊗≫ ((S.V a ⊗ S.V b) ◁ S.cup l) ⊗≫ (f ▷ S.V l) ⊗≫ 𝟙 _

private lemma rungFuse_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    rungFuse S f =
      (tensorRightHomEquiv
        (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C))
        ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ f) ≫
          (λ_ (S.V l)).hom := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [rungFuse, tensorRightHomEquiv, monoidalComp,
    SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
    ExactPairing.evaluation]

private lemma rungFuse_cap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (g : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    (rungFuse S g ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ g := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv
    (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)
  rw [rungFuse_mate]
  simpa [e, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup,
    SuQ2Data.cap, ExactPairing.coevaluation, ExactPairing.evaluation,
    ← unitors_equal] using
    e.left_inv ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ g)

/-- A rotation converts the right mate defining `rungFuse` to a left mate. -/
private lemma rungRotate_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorRightHomEquiv
      (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C))
      ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) =
      (((tensorLeftHomEquiv
        (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)) f ≫
          (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eL := tensorLeftHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let eR := tensorRightHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let q : S.V b ⊗ S.V a ⟶ 𝟙_ C ⊗ S.V l :=
    (eL f ≫ (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv
  have hrotate :
      (α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f =
        eR.symm q := by
    dsimp [eR, eL, q, tensorRightHomEquiv, tensorLeftHomEquiv]
    simp only [Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation]
    monoidal
  change eR ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) = q
  calc
    _ = eR (eR.symm q) := by rw [hrotate]
    _ = q := eR.right_inv q

private lemma rungFuse_rotate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b c : ℕ)
    (f : S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    rungFuse S (Vertex.rotate f) =
      (tensorLeftHomEquiv
        (S.V b ⊗ S.V c) (S.V a) (S.V a) (𝟙_ C)) f ≫
          (ρ_ (S.V a)).hom := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [rungFuse_mate, rungRotate_mate]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The single left mate can instead be obtained by one cup, a fuse, and one
cap. This is the small sliding step used in the rung calculation. -/
private lemma rungFuse_mate_swap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b c : ℕ)
    (g : S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv
      (S.V b ⊗ S.V c) (S.V a) (S.V a) (𝟙_ C)) g ≫ (ρ_ (S.V a)).hom =
      𝟙 _ ⊗≫ (S.cup a ▷ (S.V b ⊗ S.V c)) ⊗≫
        (S.V a ◁ (rungFuse S g ▷ S.V c)) ⊗≫
          (S.V a ◁ S.cap c) ⊗≫ 𝟙 _ := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp only [monoidalComp]
  simp
  slice_rhs 6 7 =>
    rw [← MonoidalCategory.whiskerLeft_comp, rungFuse_cap]
  dsimp [tensorLeftHomEquiv]
  monoidal

/-- Closing the two output strands of an abstract split gives the second
rotation of its covector. -/
private lemma rungRotate2_split {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a t : ℕ)
    (f : S.V t ⊗ S.V a ⊗ S.V a ⟶ 𝟙_ C) :
    Vertex.rotate (Vertex.rotate f) =
      (rungSplit S f ▷ (S.V t ⊗ S.V a)) ≫
        (α_ (S.V a) (S.V t) (S.V t ⊗ S.V a)).hom ≫
          S.V a ◁ (α_ (S.V t) (S.V t) (S.V a)).inv ≫
            S.V a ◁ (S.cap t ▷ S.V a) ≫
              S.V a ◁ (λ_ (S.V a)).hom ≫ S.cap a := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [rungSplit, Vertex.rotate, monoidalComp,
    SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
    ExactPairing.evaluation]
  monoidal

/-- A redundant cup/cap loop may be slid through two disjoint operators. -/
private lemma rungSnake_core {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A T X : C) [ExactPairing T T]
    (p : A ⟶ A ⊗ T) (k : T ⊗ X ⟶ 𝟙_ C) :
    (𝟙 (A ⊗ X) ⊗≫ (p ▷ X) ⊗≫ (A ◁ k) ⊗≫ (ρ_ A).hom) =
      (𝟙 (A ⊗ X) ⊗≫ (A ◁ (ExactPairing.coevaluation' : 𝟙_ C ⟶ T ⊗ T) ▷ X) ⊗≫
        ((A ⊗ T) ◁ k) ⊗≫ (p ▷ T) ⊗≫
          (A ◁ (ExactPairing.evaluation' : T ⊗ T ⟶ 𝟙_ C)) ⊗≫
            (ρ_ A).hom) := by
  let e := tensorLeftHomEquiv X T T (𝟙_ C)
  have h := congrArg
    (fun k' : T ⊗ X ⟶ 𝟙_ C =>
      (𝟙 (A ⊗ X) ⊗≫ (p ▷ X) ⊗≫ (A ◁ k') ⊗≫ (ρ_ A).hom))
    (e.left_inv k)
  refine h.symm.trans ?_
  let q : X ⟶ T := e k ≫ (ρ_ T).hom
  have hx := MonoidalCategory.whisker_exchange p q
  have hx' := congrArg
    (fun z : A ⊗ X ⟶ (A ⊗ T) ⊗ T =>
      z ≫ (α_ A T T).hom ≫
        (A ◁ (ExactPairing.evaluation' : T ⊗ T ⟶ 𝟙_ C)) ≫ (ρ_ A).hom)
    hx.symm
  simp [q, e, tensorLeftHomEquiv, monoidalComp] at hx' ⊢
  convert hx' using 1 <;> monoidal

/-- General rung/cap slide. The two input covectors are arbitrary; no
cyclicity or normalization is needed for the diagram deformation itself. -/
lemma agent_rung_slide {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b c t : ℕ)
    (f : S.V t ⊗ S.V a ⊗ S.V a ⟶ 𝟙_ C)
    (g : S.V t ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C) :
    ((((rungSplit S f ▷ S.V b) ⊗≫
        (S.V a ◁ rungFuse S g)) ▷ (S.V c ⊗ S.V a)) ⊗≫
      (S.V a ◁ (S.cap c ▷ S.V a)) ⊗≫ S.cap a) =
        (α_ (S.V a) (S.V b) (S.V c ⊗ S.V a)).hom ≫
          (𝟙 _ ⊗≫ (S.V a ◁ (rungFuse S (Vertex.rotate g) ▷ S.V a)) ⊗≫
            Vertex.rotate (Vertex.rotate f)) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [rungFuse_rotate, rungFuse_mate_swap, rungRotate2_split]
  simp [monoidalComp]
  slice_lhs 6 7 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, rungFuse_cap]
  slice_rhs 10 11 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← comp_whiskerRight, rungFuse_cap]
  generalize rungSplit S f = p
  have h := rungSnake_core (S.V a) (S.V t) (S.V b ⊗ S.V c) p g
  have h' := congrArg
    (fun z : S.V a ⊗ (S.V b ⊗ S.V c) ⟶ S.V a =>
      (α_ (S.V a ⊗ S.V b) (S.V c) (S.V a)).inv ≫
        ((α_ (S.V a) (S.V b) (S.V c)).hom ▷ S.V a) ≫
          (z ▷ S.V a) ≫ S.cap a) h
  simp [monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation] at h' ⊢
  convert h' using 1 <;> monoidal
private lemma close_split_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) :
    ((S.V a ⊗ S.V b) ◁ W.split l b a) ≫
      (((𝟙 (S.V a ⊗ S.V b)) ▷ (S.V b ⊗ S.V a)) ⊗≫
        (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
      (𝟙 (S.V a ⊗ S.V b)) ▷ S.V l ≫
        (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eB := tensorLeftHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let eA := tensorLeftHomEquiv (S.V b ⊗ S.V l) (S.V a) (S.V a) (𝟙_ C)
  let u : S.V b ⊗ S.V l ⟶ S.V a := eA (W.vertex a b l) ≫ (ρ_ (S.V a)).hom
  have hsplit : W.split l b a = eB u := by
    dsimp [eB, eA, u, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hB : S.V b ◁ W.split l b a ≫
      (α_ (S.V b) (S.V b) (S.V a)).inv ≫
        S.cap b ▷ S.V a ≫ (λ_ (S.V a)).hom = u := by
    rw [hsplit]
    simpa [eB, tensorLeftHomEquiv, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal] using
      eB.left_inv u
  have hunit : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
    rw [unitors_equal]
    simp
  have hA : S.V a ◁ u ≫ S.cap a = W.vertex a b l := by
    simpa [u, eA, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal, hunit] using
      eA.left_inv (W.vertex a b l)
  have hB' : S.V a ◁ S.V b ◁ W.split l b a ≫
      S.V a ◁ (α_ (S.V b) (S.V b) (S.V a)).inv ≫
        S.V a ◁ S.cap b ▷ S.V a ≫ S.V a ◁ (λ_ (S.V a)).hom ≫ S.cap a =
      S.V a ◁ u ≫ S.cap a := by
    simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
      congrArg (fun t : S.V b ⊗ S.V l ⟶ S.V a => S.V a ◁ t ≫ S.cap a) hB
  simp [monoidalComp]
  rw [hB', hA]

/-- Tensor interchange inserts an arbitrary operator before the same two-cap
mate cancellation. -/
private lemma attach_split_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ)
    (k : S.V a ⊗ S.V b ⟶ S.V a ⊗ S.V b) :
    ((S.V a ⊗ S.V b) ◁ W.split l b a) ≫
      ((k ▷ (S.V b ⊗ S.V a)) ⊗≫
        (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
      k ▷ S.V l ≫ (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have h := congrArg (fun t : (S.V a ⊗ S.V b) ⊗ S.V l ⟶ 𝟙_ C =>
    k ▷ S.V l ≫ t) (close_split_aux S W a b l)
  simpa only [monoidalComp, Category.assoc, MonoidalCategory.whisker_exchange,
    MonoidalCategory.whisker_exchange_assoc, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.comp_id] using h
lemma basis_leftcap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b c : ℕ) :
    (S.V a ◁ W.fuse b c a) ≫ S.cap a = W.vertex a b c := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorLeftHomEquiv (S.V b ⊗ S.V c) (S.V a) (S.V a) (𝟙_ C)
  have hm := rungRotate_mate S c b a (W.vertex a b c)
  rw [hW.cyclic a b c] at hm
  have hfuse : W.fuse b c a = e (W.vertex a b c) ≫ (ρ_ (S.V a)).hom := by
    change rungFuse S (W.vertex b c a) = _
    rw [rungFuse_mate, hm]
    simp [e]
  rw [hfuse]
  have hu : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
    rw [unitors_equal]
    simp
  simpa [e, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation, hu, ← unitors_equal] using
      e.left_inv (W.vertex a b c)

lemma basis_rightcup {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b c : ℕ) :
    S.cup a ≫ (S.V a ◁ W.split a b c) = W.vertexUp a b c := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e1 := tensorRightHomEquiv (𝟙_ C) (S.V c) (S.V c) (S.V a ⊗ S.V b)
  let e2 := tensorRightHomEquiv (S.V c) (S.V b) (S.V b) (S.V a)
  let e3 := tensorRightHomEquiv (S.V c ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let close (q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c) :
      S.V c ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V c) (S.V b) (S.V a)).inv ≫
      e3.symm (e2.symm ((λ_ (S.V c)).inv ≫
        e1.symm (q ≫ (α_ (S.V a) (S.V b) (S.V c)).inv)) ≫ (λ_ (S.V a)).inv)
  have hinj : Function.Injective close := by
    intro x y hxy
    rw [← cancel_mono (α_ (S.V a) (S.V b) (S.V c)).inv]
    apply e1.symm.injective
    rw [← cancel_epi (λ_ (S.V c)).inv]
    apply e2.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply e3.symm.injective
    rw [← cancel_epi (α_ (S.V c) (S.V b) (S.V a)).inv]
    exact hxy
  have hup : W.vertexUp a b c =
      e1 ((λ_ (S.V c)).hom ≫
        e2 (e3 ((α_ (S.V c) (S.V b) (S.V a)).hom ≫ W.vertex c b a) ≫
          (λ_ (S.V a)).hom)) ≫ (α_ (S.V a) (S.V b) (S.V c)).hom := by
    simp [e1, e2, e3, tensorRightHomEquiv, Vertex.vertexUp, monoidalComp,
      SuQ2Data.cup, ExactPairing.coevaluation]
    all_goals monoidal
  have hcUp : close (W.vertexUp a b c) = W.vertex c b a := by
    rw [hup]
    simp [close]
  have hcCup : close (S.cup a ≫ (S.V a ◁ W.split a b c)) =
      Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex c b a))) := by
    simp [close, e1, e2, e3, tensorRightHomEquiv, Vertex.split,
      Vertex.rotate, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation]
    all_goals monoidal
  apply hinj
  rw [hcCup, hcUp, hW.cyclic c b a, hW.cyclic b a c, hW.cyclic a c b]


section Overlap
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]

private noncomputable def pairCup {A A' B B' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B') :
    𝟙_ C ⟶ (A ⊗ B) ⊗ (B' ⊗ A') :=
  ca ⊗≫ (A ◁ cb ▷ A') ⊗≫ 𝟙 _

private lemma cup_comp {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D')
    (f : A ⟶ B) (ft : B' ⟶ A') (g : B ⟶ D) (gt : D' ⟶ B')
    (hf : ca ≫ (f ▷ A') = cb ≫ (B ◁ ft))
    (hg : cb ≫ (g ▷ B') = cd ≫ (D ◁ gt)) :
    ca ≫ ((f ≫ g) ▷ A') = cd ≫ (D ◁ (gt ≫ ft)) := by
  calc
    _ = ca ≫ (f ▷ A') ≫ (g ▷ A') := by simp
    _ = cb ≫ (B ◁ ft) ≫ (g ▷ A') := by
      rw [← Category.assoc, hf]; simp only [Category.assoc]
    _ = cb ≫ (g ▷ B') ≫ (D ◁ ft) := by rw [whisker_exchange]
    _ = cd ≫ (D ◁ gt) ≫ (D ◁ ft) := by
      rw [← Category.assoc, hg]; simp only [Category.assoc]
    _ = _ := by simp

private lemma cup_left {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') (f : B ⟶ D) (ft : D' ⟶ B')
    (hf : cb ≫ (f ▷ B') = cd ≫ (D ◁ ft)) :
    pairCup ca cb ≫ ((A ◁ f) ▷ (B' ⊗ A')) =
      pairCup ca cd ≫ ((A ⊗ D) ◁ (ft ▷ A')) := by
  calc
    _ = ca ⊗≫ (A ◁ ((cb ≫ (f ▷ B')) ▷ A')) ⊗≫ 𝟙 _ := by
      dsimp [pairCup]; monoidal
    _ = ca ⊗≫ (A ◁ ((cd ≫ (D ◁ ft)) ▷ A')) ⊗≫ 𝟙 _ := by rw [hf]
    _ = _ := by dsimp [pairCup]; monoidal

private lemma cup_right {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') (f : A ⟶ D) (ft : D' ⟶ A')
    (hf : ca ≫ (f ▷ A') = cd ≫ (D ◁ ft)) :
    pairCup ca cb ≫ ((f ▷ B) ▷ (B' ⊗ A')) =
      pairCup cd cb ≫ ((D ⊗ B) ◁ (B' ◁ ft)) := by
  have hx : (A ◁ cb) ≫ (f ▷ (B ⊗ B')) = (f ▷ (𝟙_ C)) ≫ (D ◁ cb) := by
    rw [whisker_exchange]
  have hy : ((𝟙_ C) ◁ ft) ≫ (cb ▷ A') =
      (cb ▷ D') ≫ ((B ⊗ B') ◁ ft) := by rw [whisker_exchange]
  calc
    _ = ca ⊗≫ (((A ◁ cb) ≫ (f ▷ (B ⊗ B'))) ▷ A') ⊗≫ 𝟙 _ := by
      dsimp [pairCup]; monoidal
    _ = ca ⊗≫ (((f ▷ (𝟙_ C)) ≫ (D ◁ cb)) ▷ A') ⊗≫ 𝟙 _ := by rw [hx]
    _ = (ca ≫ (f ▷ A')) ⊗≫ (D ◁ cb ▷ A') ⊗≫ 𝟙 _ := by monoidal
    _ = (cd ≫ (D ◁ ft)) ⊗≫ (D ◁ cb ▷ A') ⊗≫ 𝟙 _ := by rw [hf]
    _ = cd ⊗≫ (D ◁ (((𝟙_ C) ◁ ft) ≫ (cb ▷ A'))) ⊗≫ 𝟙 _ := by monoidal
    _ = cd ⊗≫ (D ◁ ((cb ▷ D') ≫ ((B ⊗ B') ◁ ft))) ⊗≫ 𝟙 _ := by rw [hy]
    _ = _ := by dsimp [pairCup]; monoidal

private lemma split_bend (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (l a b : ℕ) :
    W.split l a b = 𝟙 _ ⊗≫ (S.cup a ▷ S.V l) ⊗≫ (S.V a ◁ W.fuse a l b) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hm := rungRotate_mate S l a b (W.vertex b a l)
  rw [hW.cyclic b a l] at hm
  have hfuse : W.fuse a l b =
      (tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (W.vertex b a l) ≫ (ρ_ (S.V b)).hom := by
    change rungFuse S (W.vertex a l b) = _
    rw [rungFuse_mate, hm]
    simp
  rw [hfuse]
  simp [Vertex.split, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup,
    ExactPairing.coevaluation]
  all_goals monoidal

private lemma split_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (l a b : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      pairCup (S.cup a) (S.cup b) ≫ ((S.V a ⊗ S.V b) ◁ W.fuse b a l) := by
  rw [matrix_cup_split S W hW]
  rw [← basis_rightcup S W hW a b l, split_bend S W hW a b l]
  dsimp [pairCup]
  monoidal

private lemma fuse_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b l : ℕ) :
    pairCup (S.cup a) (S.cup b) ≫ (W.fuse a b l ▷ (S.V b ⊗ S.V a)) =
      S.cup l ≫ (S.V l ◁ W.split l b a) := by
  rw [basis_rightcup S W hW l b a]
  simp [pairCup, Vertex.fuse, Vertex.vertexUp, monoidalComp,
    SuQ2Data.cup, ExactPairing.coevaluation]
  all_goals monoidal

private lemma cup_assoc {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') :
    pairCup ca (pairCup cb cd) ≫ ((α_ A B D).inv ▷ ((D' ⊗ B') ⊗ A')) =
      pairCup (pairCup ca cb) cd ≫ (((A ⊗ B) ⊗ D) ◁ (α_ D' B' A').inv) := by
  dsimp [pairCup]
  monoidal

private noncomputable def tetCut (S : SuQ2Data C) (W : Vertex S)
    (a b c d j l : ℕ) : S.V a ⟶ S.V a :=
  W.split a b l ≫ (S.V b ◁ W.split l c d) ≫
    (α_ (S.V b) (S.V c) (S.V d)).inv ≫
      (W.fuse b c j ▷ S.V d) ≫ W.fuse j d a

private lemma cut_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b c d j l : ℕ) :
    S.cup a ≫ (tetCut S W a b c d j l ▷ S.V a) =
      S.cup a ≫ (S.V a ◁ tetCut S W a d c b l j) := by
  have h1 := split_cup S W hW a b l
  have h2 := cup_left (S.cup b) (S.cup l)
    (pairCup (S.cup c) (S.cup d)) (W.split l c d) (W.fuse d c l)
    (split_cup S W hW l c d)
  have h2a := cup_comp
    (pairCup (S.cup b) (S.cup l))
    (pairCup (S.cup b) (pairCup (S.cup c) (S.cup d)))
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (S.V b ◁ W.split l c d) (W.fuse d c l ▷ S.V b)
    (α_ (S.V b) (S.V c) (S.V d)).inv
    (α_ (S.V d) (S.V c) (S.V b)).inv h2
    (cup_assoc (S.cup b) (S.cup c) (S.cup d))
  have h3 := cup_right (pairCup (S.cup b) (S.cup c)) (S.cup d) (S.cup j)
    (W.fuse b c j) (W.split j c b) (fuse_cup S W hW b c j)
  have h4 := fuse_cup S W hW j d a
  have h12 := cup_comp (S.cup a) (pairCup (S.cup b) (S.cup l))
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (W.split a b l) (W.fuse l b a)
    ((S.V b ◁ W.split l c d) ≫ (α_ (S.V b) (S.V c) (S.V d)).inv)
    ((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) h1 h2a
  have h123 := cup_comp (S.cup a)
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (pairCup (S.cup j) (S.cup d))
    (W.split a b l ≫ ((S.V b ◁ W.split l c d) ≫
      (α_ (S.V b) (S.V c) (S.V d)).inv))
    (((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) ≫
      W.fuse l b a)
    (W.fuse b c j ▷ S.V d) (S.V d ◁ W.split j c b) h12 h3
  have h1234 := cup_comp (S.cup a) (pairCup (S.cup j) (S.cup d)) (S.cup a)
    ((W.split a b l ≫ ((S.V b ◁ W.split l c d) ≫
      (α_ (S.V b) (S.V c) (S.V d)).inv)) ≫ (W.fuse b c j ▷ S.V d))
    ((S.V d ◁ W.split j c b) ≫
      (((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) ≫ W.fuse l b a))
    (W.fuse j d a) (W.split a d j) h123 h4
  simpa only [tetCut, Category.assoc] using h1234

private lemma cut_trace (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b c d j l : ℕ) :
    S.cup a ≫ (S.V a ◁ tetCut S W a b c d j l) ≫ S.cap a =
      W.X a b c d l ≫ W.Hcov a b c d j := by
  simp only [tetCut, whiskerLeft_comp, Category.assoc]
  rw [basis_leftcap S W hW a j d]
  rw [← Category.assoc (S.cup a) (S.V a ◁ W.split a b l), basis_rightcup S W hW]
  simp [Vertex.X, Vertex.Hcov, monoidalComp, MonoidalCategory.tensorHom_def]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l),
    matrix_cup_split S W hW]
  monoidal


end Overlap

section MatrixBridges
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]

private lemma generalized_rung (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (a b c t : ℕ) :
    ((((W.split a a t ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse t b c)) ▷
        (S.V c ⊗ S.V a)) ⊗≫
      (S.V a ◁ (S.cap c ▷ S.V a)) ⊗≫ S.cap a) =
      (α_ (S.V a) (S.V b) (S.V c ⊗ S.V a)).hom ≫ W.Hcov a b c a t := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have h := agent_rung_slide S a b c t (W.vertex t a a) (W.vertex t b c)
  rw [hW.cyclic t a a, hW.cyclic a a t, hW.cyclic t b c] at h
  simpa only [rungSplit, rungFuse, Vertex.split, Vertex.fuse, Vertex.Hcov] using h

private lemma attach_general (S : SuQ2Data C) (W : Vertex S) (a b c l : ℕ)
    (r : S.V a ⊗ S.V b ⟶ S.V a ⊗ S.V c) :
    ((S.V a ⊗ S.V b) ◁ W.split l c a) ≫
      ((r ▷ (S.V c ⊗ S.V a)) ⊗≫
        (S.V a ◁ (S.cap c ▷ S.V a)) ⊗≫ S.cap a) =
      r ▷ S.V l ≫ (α_ (S.V a) (S.V c) (S.V l)).hom ≫ W.vertex a c l := by
  have h := congrArg (fun z : (S.V a ⊗ S.V c) ⊗ S.V l ⟶ 𝟙_ C =>
    r ▷ S.V l ≫ z) (close_split_aux S W a c l)
  simpa only [monoidalComp, Category.assoc, MonoidalCategory.whisker_exchange,
    MonoidalCategory.whisker_exchange_assoc, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.comp_id] using h

lemma leftTet_swapped (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (a d j k : ℕ) :
    MatrixTriangle.leftTet S W a d j k = W.tet a a j k d 2 := by
  have hr := generalized_rung S W hW a k j 2
  have ha := attach_general S W a k j d
    ((W.split a a 2 ▷ S.V k) ⊗≫ (S.V a ◁ W.fuse 2 k j))
  rw [hr] at ha
  have h := congrArg (fun z : (S.V a ⊗ S.V k) ⊗ S.V d ⟶ 𝟙_ C =>
    W.vertexUp a k d ≫ (α_ (S.V a) (S.V k) (S.V d)).inv ≫ z) ha
  simp [MatrixTriangle.leftTet, MatrixTriangle.leftClose, Vertex.tet,
    Vertex.X, monoidalComp, MonoidalCategory.tensorHom_def]
  rw [← Category.assoc (S.cup d) (W.split d a k ▷ S.V d), matrix_cup_split S W hW]
  simpa [monoidalComp] using h.symm

private lemma split_right_bend (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (l a b : ℕ) :
    W.split l a b = 𝟙 _ ⊗≫ (S.V l ◁ S.cup b) ⊗≫ (W.fuse l b a ▷ S.V b) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  have hsplit : W.split l a b = eLa (eLb (W.vertex b a l) ≫ (ρ_ (S.V b)).hom) := by
    dsimp [eLa, eLb, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have h3 : Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex l b a))) = W.vertex l b a := by
    rw [hW.cyclic l b a, hW.cyclic b a l, hW.cyclic a l b]
  have hm := matrix_rotate_mates S a b l (W.vertex l b a) h3
  rw [hsplit, ← hW.cyclic l b a, hm]
  simp [eRb, eRa, tensorRightHomEquiv, Vertex.fuse, monoidalComp,
    SuQ2Data.cup, ExactPairing.coevaluation]
  all_goals monoidal

private lemma bend_square (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (b c k : ℕ) :
    (S.V c ◁ W.split b b 2) ⊗≫ (W.fuse c b k ▷ S.V 2) =
      (W.split c k b ▷ S.V b) ⊗≫ (S.V k ◁ W.fuse b b 2) := by
  have hx := whisker_exchange (W.fuse c b k) (W.fuse b b 2)
  calc
    _ = 𝟙 _ ⊗≫ (S.V c ◁ S.cup b ▷ S.V b) ⊗≫
        (((S.V c ⊗ S.V b) ◁ W.fuse b b 2) ≫ (W.fuse c b k ▷ S.V 2)) := by
      rw [split_bend S W hW b b 2]; monoidal
    _ = 𝟙 _ ⊗≫ (S.V c ◁ S.cup b ▷ S.V b) ⊗≫
        ((W.fuse c b k ▷ (S.V b ⊗ S.V b)) ≫ (S.V k ◁ W.fuse b b 2)) := by rw [hx]
    _ = _ := by rw [split_right_bend S W hW c k b]; monoidal

private lemma reverse_cut (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (b c j k : ℕ) :
    S.cup j ≫ (S.V j ◁ tetCut S W j c b 2 k b) ≫ S.cap j =
      S.cup b ≫ (tetCut S W b j k b 2 c ▷ S.V b) ≫ S.cap b := by
  have hsq := bend_square S W hW b c k
  have hup : W.vertexUp j c b = S.cup b ≫ (W.split b j c ▷ S.V b) ≫
      (α_ (S.V j) (S.V c) (S.V b)).hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun z : 𝟙_ C ⟶ (S.V j ⊗ S.V c) ⊗ S.V b =>
        z ≫ (α_ (S.V j) (S.V c) (S.V b)).hom)
        (matrix_cup_split S W hW j c b).symm
  have htail : ((S.V j ⊗ S.V k) ◁ W.fuse b b 2) ⊗≫ W.vertex j k 2 =
      (W.fuse j k 2 ▷ (S.V b ⊗ S.V b)) ⊗≫
        (W.fuse 2 b b ▷ S.V b) ⊗≫ S.cap b := by
    have hx := whisker_exchange (W.fuse j k 2) (W.fuse b b 2)
    have hlast : W.vertex 2 b b =
        (α_ (S.V 2) (S.V b) (S.V b)).inv ≫
          (W.fuse 2 b b ▷ S.V b) ≫ S.cap b := by
      calc
        _ = (α_ (S.V 2) (S.V b) (S.V b)).inv ≫
            ((α_ (S.V 2) (S.V b) (S.V b)).hom ≫ W.vertex 2 b b) := by simp
        _ = _ := by rw [← matrix_fuse_cap S W 2 b b]
    calc
      _ = ((S.V j ⊗ S.V k) ◁ W.fuse b b 2) ≫
          (α_ (S.V j) (S.V k) (S.V 2)).hom ≫ W.vertex j k 2 := by monoidal
      _ = ((S.V j ⊗ S.V k) ◁ W.fuse b b 2) ≫
          (W.fuse j k 2 ▷ S.V 2) ≫ S.cap 2 := by
        rw [← matrix_fuse_cap S W j k 2]
      _ = (W.fuse j k 2 ▷ (S.V b ⊗ S.V b)) ≫ (S.V 2 ◁ W.fuse b b 2) ≫ S.cap 2 := by
        rw [← Category.assoc, hx, Category.assoc]
      _ = (W.fuse j k 2 ▷ (S.V b ⊗ S.V b)) ≫ W.vertex 2 b b := by
        rw [basis_leftcap S W hW 2 b b]
      _ = (W.fuse j k 2 ▷ (S.V b ⊗ S.V b)) ≫
          (α_ (S.V 2) (S.V b) (S.V b)).inv ≫
            (W.fuse 2 b b ▷ S.V b) ≫ S.cap b := by rw [hlast]
      _ = _ := by monoidal
  simp only [tetCut, whiskerLeft_comp, Category.assoc]
  rw [basis_leftcap S W hW j k 2]
  rw [← Category.assoc (S.cup j) (S.V j ◁ W.split j c b), basis_rightcup S W hW]
  calc
    _ = W.vertexUp j c b ⊗≫ (S.V j ◁
        ((S.V c ◁ W.split b b 2) ⊗≫ (W.fuse c b k ▷ S.V 2))) ⊗≫ W.vertex j k 2 := by monoidal
    _ = W.vertexUp j c b ⊗≫ (S.V j ◁
        ((W.split c k b ▷ S.V b) ⊗≫ (S.V k ◁ W.fuse b b 2))) ⊗≫ W.vertex j k 2 := by rw [hsq]
    _ = (W.vertexUp j c b ⊗≫ (S.V j ◁ W.split c k b ▷ S.V b)) ⊗≫
        (((S.V j ⊗ S.V k) ◁ W.fuse b b 2) ⊗≫ W.vertex j k 2) := by monoidal
    _ = (W.vertexUp j c b ⊗≫ (S.V j ◁ W.split c k b ▷ S.V b)) ⊗≫
        ((W.fuse j k 2 ▷ (S.V b ⊗ S.V b)) ⊗≫ (W.fuse 2 b b ▷ S.V b) ⊗≫ S.cap b) := by rw [htail]
    _ = _ := by
      rw [hup]
      monoidal

lemma rightTet_identification (S : SuQ2Data C) (W : Vertex S)
    (hS : SuQ2Axioms S) (hW : VertexNormalized W) (b c j k : ℕ) :
    MatrixTriangle.rightTet S W b c j k = W.tet b b k j c 2 := by
  have hs := congrArg (fun z : 𝟙_ C ⟶ S.V j ⊗ S.V j => z ≫ S.cap j)
    (cut_cup S W hW j 2 b c b k)
  have ht : S.cup b ≫ (tetCut S W b j k b 2 c ▷ S.V b) ≫ S.cap b =
      S.cup b ≫ (S.V b ◁ tetCut S W b j k b 2 c) ≫ S.cap b := by
    obtain ⟨s, he, _⟩ := hS.simple b (tetCut S W b j k b 2 c)
    rw [he]; simp
  calc
    _ = S.cup j ≫ (S.V j ◁ tetCut S W j c b 2 k b) ≫ S.cap j := by
      convert hs using 1 <;>
        simp [MatrixTriangle.rightTet, MatrixTriangle.right, tetCut, monoidalComp] <;> monoidal
    _ = S.cup b ≫ (tetCut S W b j k b 2 c ▷ S.V b) ≫ S.cap b := reverse_cut S W hW b c j k
    _ = S.cup b ≫ (S.V b ◁ tetCut S W b j k b 2 c) ≫ S.cap b := ht
    _ = W.X b j k b c ≫ W.Hcov b j k b 2 := cut_trace S W hW b j k b 2 c
    _ = W.tet b b k j c 2 := by simp [Vertex.tet]

end MatrixBridges

end QuantumSixJ.Network

namespace QuantumSixJ
def diagonalEntry (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ j ≠ 0 then
    -h a b c d j * ⟬2⟭ * Λ a j d * Λ b j c / (⟬j⟭ * ⟬j + 2⟭)
  else 0

def Lp2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j + 2) then
    h a b c d (j + 2) * ⟬(a + d - j) / 2⟭ * ⟬(b + c - j) / 2⟭
  else 0

def Lm2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j - 2) then
    h a b c d j * ⟬(a + d - (j - 2)) / 2⟭ * ⟬(b + c - (j - 2)) / 2⟭
  else 0

end QuantumSixJ
private theorem tet_special_evaluations :
    (∀ a b l : ℤ, 0 < a → 0 < b → Admissible a b l →
      ⟬a⟭ * ⟬b⟭ * tetSum a a b b l 2 = θ a b l * Λ a b l) ∧
    (∀ a d j : ℤ, 0 < a → Admissible a d j → Admissible a d (j + 2) →
      ⟬a⟭ * tetSum a a (j + 2) j d 2 =
        ⟬(a + d - j) / 2⟭ * θ (j + 2) a d) := by
  constructor
  · exact QuantumSixJ.tet_two_evaluations.2.2.1
  · intro a d j ha hj hj2
    have h1 : Admissible a (j + 2) d := by dsimp [Admissible] at *; omega
    have h2 : Admissible a j d := by dsimp [Admissible] at *; omega
    simpa only [min_eq_right (show j ≤ j + 2 by omega),
      max_eq_left (show j ≤ j + 2 by omega)] using
      QuantumSixJ.tet_two_evaluations.2.2.2.1 a (j + 2) j d ha h1 h2 (Or.inl rfl)


namespace QuantumSixJ.Network
namespace MatrixScalars
private lemma qzero_aux : ⟬(0 : ℤ)⟭ = 0 := by simp [qInt]
private lemma fzero_aux : ⟬(0 : ℤ)⟭! = 1 := by norm_num [qFactorial]

private lemma qone_aux : ⟬(1 : ℤ)⟭ = 1 := by
  simpa [qInt] using div_self q_denominator_ne_zero

private lemma fone_aux : ⟬(1 : ℤ)⟭! = 1 := by simp [qFactorial, qone_aux]

private lemma ftwo_aux : ⟬(2 : ℤ)⟭! = ⟬(2 : ℤ)⟭ := by
  have hi : Finset.Icc (1 : ℤ) 2 = {1, 2} := by decide
  simp [qFactorial, hi, qone_aux]

private lemma fstep_aux (n : ℤ) (hn : 0 ≤ n) : ⟬n + 1⟭! = ⟬n + 1⟭ * ⟬n⟭! := by
  have hset : Finset.Icc (1 : ℤ) (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc (1 : ℤ) n := by
    intro hk
    have := (Finset.mem_Icc.mp hk).2
    omega
  simp only [qFactorial, if_neg (show ¬n + 1 < 0 by omega), if_neg (not_lt.mpr hn)]
  rw [hset, Finset.prod_insert hnot]

private lemma fprev_aux (n : ℤ) (hn : 0 < n) : ⟬n⟭! = ⟬n⟭ * ⟬n - 1⟭! := by
  simpa using fstep_aux (n - 1) (by omega)

private lemma adm_swap_aux {a b c : ℤ} (h : Admissible a b c) : Admissible b a c := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  exact ⟨hb, ha, hc, by omega, by omega, by omega, by omega⟩

private lemma adm_swap_right_aux {a b c : ℤ} (h : Admissible a b c) : Admissible a c b := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  exact ⟨ha, hc, hb, by omega, by omega, by omega, by omega⟩

private lemma theta_swap_right_aux (a b c : ℤ) (h : Admissible a b c) : θ a b c = θ a c b := by
  have hc := adm_swap_right_aux h
  simp [θ, h, hc, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

private lemma theta_central_diag_aux (j : ℤ) (hj : 0 < j) :
    θ 2 j j = -⟬j + 2⟭ / (⟬(2 : ℤ)⟭ * ⟬j⟭) * Δ j := by
  have ha : Admissible 2 j j := by
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [θ, if_pos ha, Δ, if_pos (by omega : 0 ≤ j)]
  dsimp only
  rw [show (2 + j + j) / 2 = j + 1 by omega]
  change (-1 : Scalar) ^ (j + 1) * ⟬j + 1 + 1⟭! * ⟬j + 1 - 2⟭! *
      ⟬j + 1 - j⟭! * ⟬j + 1 - j⟭! /
      (⟬(2 : ℤ)⟭! * ⟬j⟭! * ⟬j⟭!) =
    -⟬j + 2⟭ / (⟬(2 : ℤ)⟭ * ⟬j⟭) * ((-1 : Scalar) ^ j * ⟬j + 1⟭)
  have hf2 : ⟬j + 2⟭! = ⟬j + 2⟭ * (⟬j + 1⟭ * ⟬j⟭!) := by
    rw [show j + 2 = (j + 1) + 1 by omega, fstep_aux (j + 1) (by omega),
      fstep_aux j (by omega)]
  have hfj : ⟬j⟭! = ⟬j⟭ * ⟬j - 1⟭! := fprev_aux j hj
  have hsign : (-1 : Scalar) ^ (j + 1) = -((-1 : Scalar) ^ j) := by
    rw [zpow_add₀ (by norm_num : (-1 : Scalar) ≠ 0)]
    simp
  simp only [show j + 1 + 1 = j + 2 by omega, show j + 1 - 2 = j - 1 by omega,
    show j + 1 - j = 1 by omega, fone_aux, ftwo_aux, hf2, hfj, hsign]
  field_simp [qInt_ne_zero j (by omega), qInt_ne_zero 2 (by omega),
    qFactorial_ne_zero (j - 1) (by omega)]
  <;> ring

private lemma tet_diag_zero_aux (a d j : ℤ) (hc : ¬ Admissible a d j) :
    tetSum a a j j d 2 = 0 := by
  rw [tetSum, if_neg]
  rintro ⟨hh, _⟩
  exact hc (adm_swap_right_aux hh.1)

private lemma lambda_zero_left_aux (b l : ℤ) (h : Admissible 0 b l) : Λ 0 b l = 0 := by
  rw [Λ, if_pos h]
  have hbl : b = l := by rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩; omega
  rw [show (0 + b - l) / 2 = 0 by rw [hbl]; simp]
  simp only [zero_add, zero_sub, neg_zero, add_zero, sub_zero]
  rw [show (-b + l) / 2 = 0 by rw [hbl]; simp]
  rw [qzero_aux]
  ring

private lemma lambda_zero_right_aux (a l : ℤ) (h : Admissible a 0 l) : Λ a 0 l = 0 := by
  rw [Λ, if_pos h]
  have hal : a = l := by rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩; omega
  rw [show (-a + 0 + l) / 2 = 0 by rw [hal]; simp]
  simp only [zero_add, zero_sub, neg_zero, add_zero, sub_zero]
  rw [show (a - l) / 2 = 0 by rw [hal]; simp]
  rw [qzero_aux]
  ring

private lemma horizontal_diag_valid_aux (a b c d j : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hj : 0 < j) (hAdm : hAdmissible (a : ℤ) b c d j) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) j *
      (tetSum (a : ℤ) a j j d 2 * tetSum (b : ℤ) b j j c 2) = diagonalEntry a b c d j := by
  have hadj : Admissible (a : ℤ) j d := adm_swap_right_aux hAdm.1
  have hbjc : Admissible (b : ℤ) j c := adm_swap_right_aux hAdm.2
  have hTa0 := (tet_special_evaluations).1 (a : ℤ) (j : ℤ) (d : ℤ)
    (by exact_mod_cast ha) (by exact_mod_cast hj) hadj
  have hTb0 := (tet_special_evaluations).1 (b : ℤ) (j : ℤ) (c : ℤ)
    (by exact_mod_cast hb) (by exact_mod_cast hj) hbjc
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hj0 : (j : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hqa := qInt_ne_zero (a : ℤ) ha0
  have hqb := qInt_ne_zero (b : ℤ) hb0
  have hqj := qInt_ne_zero (j : ℤ) hj0
  have hTa : tetSum (a : ℤ) a j j d 2 =
      θ (a : ℤ) j d * Λ (a : ℤ) j d / (⟬(a : ℤ)⟭ * ⟬(j : ℤ)⟭) := by
    apply (eq_div_iff (mul_ne_zero hqa hqj)).2
    calc
      _ = ⟬(a : ℤ)⟭ * ⟬(j : ℤ)⟭ * tetSum (a : ℤ) a j j d 2 := by ring
      _ = _ := hTa0
  have hTb : tetSum (b : ℤ) b j j c 2 =
      θ (b : ℤ) j c * Λ (b : ℤ) j c / (⟬(b : ℤ)⟭ * ⟬(j : ℤ)⟭) := by
    apply (eq_div_iff (mul_ne_zero hqb hqj)).2
    calc
      _ = ⟬(b : ℤ)⟭ * ⟬(j : ℤ)⟭ * tetSum (b : ℤ) b j j c 2 := by ring
      _ = _ := hTb0
  rw [hTa, hTb, theta_swap_right_aux (a : ℤ) j d hadj,
    theta_swap_right_aux (b : ℤ) j c hbjc,
    theta_central_diag_aux (j : ℤ) (by exact_mod_cast hj)]
  rw [diagonalEntry, if_pos ⟨hAdm, by exact_mod_cast (Nat.ne_of_gt hj)⟩]
  rw [h, if_pos hAdm]
  field_simp [hqa, hqb, hqj, qInt_ne_zero 2 (by omega),
    qInt_ne_zero ((j : ℤ) + 2) (by omega), delta_ne_zero (j : ℤ) (by omega)]
  <;> ring

/-- The diagonal scalar closed-network value, including its intentional zero
extensions and the exceptional `j = 0` case. -/
private lemma horizontal_diag_scalar_aux (a b c d j : ℕ) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) j *
      (tetSum (a : ℤ) a j j d 2 * tetSum (b : ℤ) b j j c 2) = diagonalEntry a b c d j := by
  by_cases hj : j = 0
  · subst j
    norm_num [diagonalEntry, θ, Admissible]
  by_cases hAdm : hAdmissible (a : ℤ) b c d j
  · by_cases ha : a = 0
    · subst a
      rw [diagonalEntry, if_pos ⟨hAdm, by exact_mod_cast hj⟩]
      have hΛ := lambda_zero_left_aux (j : ℤ) (d : ℤ) (adm_swap_right_aux hAdm.1)
      simp only [Nat.cast_zero]
      rw [qzero_aux, hΛ]
      ring
    by_cases hb : b = 0
    · subst b
      rw [diagonalEntry, if_pos ⟨hAdm, by exact_mod_cast hj⟩]
      have hΛ := lambda_zero_left_aux (j : ℤ) (c : ℤ) (adm_swap_right_aux hAdm.2)
      simp only [Nat.cast_zero]
      rw [qzero_aux, hΛ]
      ring
    exact horizontal_diag_valid_aux a b c d j (Nat.pos_of_ne_zero ha)
      (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hj) hAdm
  · rw [diagonalEntry, if_neg (fun h => hAdm h.1)]
    by_cases had : Admissible (a : ℤ) d j
    · have hbc : ¬ Admissible (b : ℤ) c j := fun h => hAdm ⟨had, h⟩
      rw [tet_diag_zero_aux (b : ℤ) c j hbc]
      simp
    · rw [tet_diag_zero_aux (a : ℤ) d j had]
      simp

private lemma off_fzero_aux : ⟬(0 : ℤ)⟭! = 1 := by norm_num [qFactorial]

private lemma off_qone_aux : ⟬(1 : ℤ)⟭ = 1 := by
  simpa [qInt] using div_self q_denominator_ne_zero

private lemma off_ftwo_aux : ⟬(2 : ℤ)⟭! = ⟬(2 : ℤ)⟭ := by
  have hi : Finset.Icc (1 : ℤ) 2 = {1, 2} := by decide
  simp [qFactorial, hi, off_qone_aux]

private lemma off_fstep_aux (n : ℤ) (hn : 0 ≤ n) : ⟬n + 1⟭! = ⟬n + 1⟭ * ⟬n⟭! := by
  have hset : Finset.Icc (1 : ℤ) (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc (1 : ℤ) n := by
    intro hk
    have := (Finset.mem_Icc.mp hk).2
    omega
  simp only [qFactorial, if_neg (show ¬n + 1 < 0 by omega), if_neg (not_lt.mpr hn)]
  rw [hset, Finset.prod_insert hnot]

private lemma off_adm_swap_aux {a b c : ℤ} (h : Admissible a b c) : Admissible b a c := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  exact ⟨hb, ha, hc, by omega, by omega, by omega, by omega⟩

private lemma off_adm_swap_right_aux {a b c : ℤ} (h : Admissible a b c) : Admissible a c b := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  exact ⟨ha, hc, hb, by omega, by omega, by omega, by omega⟩

private lemma off_adm_cycle_aux {a b c : ℤ} (h : Admissible a b c) : Admissible c a b := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  exact ⟨hc, ha, hb, by omega, by omega, by omega, by omega⟩

private lemma off_theta_cycle_aux (a b c : ℤ) (h : Admissible a b c) : θ a b c = θ c a b := by
  have hc := off_adm_cycle_aux h
  simp [θ, h, hc, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

private lemma off_theta_central_off_aux (j : ℤ) (hj : 0 ≤ j) : θ 2 j (j + 2) = Δ (j + 2) := by
  have ha : Admissible 2 j (j + 2) := by
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [θ, if_pos ha, Δ, if_pos (by omega : 0 ≤ j + 2)]
  dsimp only
  rw [show (2 + j + (j + 2)) / 2 = j + 2 by omega]
  change (-1 : Scalar) ^ (j + 2) * ⟬j + 2 + 1⟭! * ⟬j + 2 - 2⟭! *
      ⟬j + 2 - j⟭! * ⟬j + 2 - (j + 2)⟭! /
      (⟬(2 : ℤ)⟭! * ⟬j⟭! * ⟬j + 2⟭!) =
    (-1 : Scalar) ^ (j + 2) * ⟬j + 2 + 1⟭
  have hf3 : ⟬j + 3⟭! = ⟬j + 3⟭ * ⟬j + 2⟭! := by
    have hf := off_fstep_aux (j + 2) (by omega)
    rw [show j + 2 + 1 = j + 3 by omega] at hf
    exact hf
  simp only [show j + 2 + 1 = j + 3 by omega, show j + 2 - 2 = j by omega,
    show j + 2 - j = 2 by omega, show j + 2 - (j + 2) = 0 by omega,
    off_fzero_aux, off_ftwo_aux, hf3]
  field_simp [qInt_ne_zero 2 (by omega), qFactorial_ne_zero j hj,
    qFactorial_ne_zero (j + 2) (by omega)]
  <;> ring

private lemma off_tet_upper_zero_aux (a d j : ℤ)
    (hc : ¬ (Admissible a d j ∧ Admissible a d (j + 2))) :
    tetSum a a (j + 2) j d 2 = 0 := by
  rw [tetSum, if_neg]
  rintro ⟨hh, _⟩
  exact hc ⟨off_adm_swap_right_aux hh.1, off_adm_swap_right_aux hh.2⟩

private lemma off_tet_lower_zero_aux (a d j : ℤ)
    (hc : ¬ (Admissible a d j ∧ Admissible a d (j + 2))) :
    tetSum a a j (j + 2) d 2 = 0 := by
  rw [tetSum, if_neg]
  rintro ⟨hh, _⟩
  exact hc ⟨off_adm_swap_right_aux hh.2, off_adm_swap_right_aux hh.1⟩

private lemma off_tet_swap_cd_aux (a c d j l : ℤ) : tetSum a a c d j l = tetSum a a d c j l := by
  have hadm : (hAdmissible a a c d j ∧ vAdmissible a a c d l) ↔
      (hAdmissible a a d c j ∧ vAdmissible a a d c l) := by
    constructor
    · rintro ⟨⟨had, hac⟩, ⟨haal, hcdl⟩⟩
      exact ⟨⟨hac, had⟩, ⟨haal, off_adm_swap_aux hcdl⟩⟩
    · rintro ⟨⟨hac, had⟩, ⟨haal, hdc⟩⟩
      exact ⟨⟨had, hac⟩, ⟨haal, off_adm_swap_aux hdc⟩⟩
  have hA : tetA a a d c j l = ![(tetA a a c d j l) 1, (tetA a a c d j l) 0,
      (tetA a a c d j l) 2, (tetA a a c d j l) 3] := by
    ext i
    fin_cases i <;> simp [tetA] <;> congr 1 <;> ring
  have hB : tetB a a d c j l = ![(tetB a a c d j l) 1, (tetB a a c d j l) 0,
      (tetB a a c d j l) 2] := by
    ext i
    fin_cases i <;> simp [tetB] <;> congr 1 <;> ring
  have hs (S : ℤ) : tetSummand a a d c j l S = tetSummand a a c d j l S := by
    simp only [tetSummand, hA, hB, Fin.prod_univ_succ]
    simp
    ring
  by_cases h : hAdmissible a a c d j ∧ vAdmissible a a c d l
  · rw [tetSum, if_pos h, tetSum, if_pos (hadm.mp h)]
    simp_rw [hs]
    rw [show a + a + d + c + j + l = a + a + c + d + j + l by ring]
    have f41 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := by decide
    have f42 : (Fin.succ (Fin.succ (0 : Fin 2)) : Fin 4) = 2 := by decide
    have f43 : (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) : Fin 4) = 3 := by decide
    have f42' : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := by decide
    have f43' : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := by decide
    have f31 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
    have f32 : (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = 2 := by decide
    simp only [hA, hB, Fin.prod_univ_succ, f41, f42, f43, f42', f43', f31, f32,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    ring
  · rw [tetSum, if_neg h, tetSum, if_neg]
    exact fun h' => h (hadm.mpr h')

private lemma off_horizontal_upper_valid_aux (a b c d j : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hj : hAdmissible (a : ℤ) b c d j)
    (hj2 : hAdmissible (a : ℤ) b c d (j + 2)) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) (j + 2) *
      (tetSum (a : ℤ) a (j + 2) j d 2 * tetSum (b : ℤ) b (j + 2) j c 2) = Lp2 a b c d j := by
  have hTa0 := (tet_special_evaluations).2 (a : ℤ) (d : ℤ) (j : ℤ)
    (by exact_mod_cast ha) hj.1 hj2.1
  have hTb0 := (tet_special_evaluations).2 (b : ℤ) (c : ℤ) (j : ℤ)
    (by exact_mod_cast hb) hj.2 hj2.2
  have hqa := qInt_ne_zero (a : ℤ) (by exact_mod_cast (Nat.ne_of_gt ha))
  have hqb := qInt_ne_zero (b : ℤ) (by exact_mod_cast (Nat.ne_of_gt hb))
  have hTa : tetSum (a : ℤ) a (j + 2) j d 2 =
      ⟬((a : ℤ) + d - j) / 2⟭ * θ ((j : ℤ) + 2) a d / ⟬(a : ℤ)⟭ := by
    apply (eq_div_iff hqa).2
    calc
      _ = ⟬(a : ℤ)⟭ * tetSum (a : ℤ) a (j + 2) j d 2 := by ring
      _ = _ := hTa0
  have hTb : tetSum (b : ℤ) b (j + 2) j c 2 =
      ⟬((b : ℤ) + c - j) / 2⟭ * θ ((j : ℤ) + 2) b c / ⟬(b : ℤ)⟭ := by
    apply (eq_div_iff hqb).2
    calc
      _ = ⟬(b : ℤ)⟭ * tetSum (b : ℤ) b (j + 2) j c 2 := by ring
      _ = _ := hTb0
  rw [hTa, hTb, ← off_theta_cycle_aux (a : ℤ) d ((j : ℤ) + 2) hj2.1,
    ← off_theta_cycle_aux (b : ℤ) c ((j : ℤ) + 2) hj2.2]
  rw [off_theta_central_off_aux (j : ℤ) (by omega), Lp2, if_pos ⟨hj, hj2⟩, h, if_pos hj2]
  field_simp [hqa, hqb, delta_ne_zero ((j : ℤ) + 2) (by omega)]
  <;> ring

private lemma off_horizontal_lower_valid_aux (a b c d j : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hj : hAdmissible (a : ℤ) b c d j)
    (hj2 : hAdmissible (a : ℤ) b c d (j + 2)) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) (j + 2) *
      (tetSum (a : ℤ) a j (j + 2) d 2 * tetSum (b : ℤ) b j (j + 2) c 2) =
        Lm2 a b c d ((j : ℤ) + 2) := by
  have hTa0 : ⟬(a : ℤ)⟭ * tetSum (a : ℤ) a j (j + 2) d 2 =
      ⟬((a : ℤ) + d - j) / 2⟭ * θ ((j : ℤ) + 2) a d := by
    rw [← off_tet_swap_cd_aux (a : ℤ) ((j : ℤ) + 2) j d 2]
    exact (tet_special_evaluations).2 (a : ℤ) d j (by exact_mod_cast ha) hj.1 hj2.1
  have hTb0 : ⟬(b : ℤ)⟭ * tetSum (b : ℤ) b j (j + 2) c 2 =
      ⟬((b : ℤ) + c - j) / 2⟭ * θ ((j : ℤ) + 2) b c := by
    rw [← off_tet_swap_cd_aux (b : ℤ) ((j : ℤ) + 2) j c 2]
    exact (tet_special_evaluations).2 (b : ℤ) c j (by exact_mod_cast hb) hj.2 hj2.2
  have hqa := qInt_ne_zero (a : ℤ) (by exact_mod_cast (Nat.ne_of_gt ha))
  have hqb := qInt_ne_zero (b : ℤ) (by exact_mod_cast (Nat.ne_of_gt hb))
  have hTa : tetSum (a : ℤ) a j (j + 2) d 2 =
      ⟬((a : ℤ) + d - j) / 2⟭ * θ ((j : ℤ) + 2) a d / ⟬(a : ℤ)⟭ :=
    (eq_div_iff hqa).2 (by calc
      _ = ⟬(a : ℤ)⟭ * tetSum (a : ℤ) a j (j + 2) d 2 := by ring
      _ = _ := hTa0)
  have hTb : tetSum (b : ℤ) b j (j + 2) c 2 =
      ⟬((b : ℤ) + c - j) / 2⟭ * θ ((j : ℤ) + 2) b c / ⟬(b : ℤ)⟭ :=
    (eq_div_iff hqb).2 (by calc
      _ = ⟬(b : ℤ)⟭ * tetSum (b : ℤ) b j (j + 2) c 2 := by ring
      _ = _ := hTb0)
  have hjm : (j : ℤ) + 2 - 2 = (j : ℤ) := by ring
  rw [hTa, hTb, ← off_theta_cycle_aux (a : ℤ) d ((j : ℤ) + 2) hj2.1,
    ← off_theta_cycle_aux (b : ℤ) c ((j : ℤ) + 2) hj2.2]
  rw [off_theta_central_off_aux (j : ℤ) (by omega), Lm2,
    if_pos ⟨hj2, by simpa only [hjm] using hj⟩]
  simp only [hjm]
  rw [h, if_pos hj2]
  field_simp [hqa, hqb, delta_ne_zero ((j : ℤ) + 2) (by omega)]
  <;> ring

/-- Upper neighboring scalar value, with zero extensions. -/
private lemma off_horizontal_upper_scalar_aux (a b c d j : ℕ) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) (j + 2) *
      (tetSum (a : ℤ) a (j + 2) j d 2 * tetSum (b : ℤ) b (j + 2) j c 2) = Lp2 a b c d j := by
  by_cases hpa : Admissible (a : ℤ) d j ∧ Admissible (a : ℤ) d (j + 2)
  · by_cases hpb : Admissible (b : ℤ) c j ∧ Admissible (b : ℤ) c (j + 2)
    · have hj : hAdmissible (a : ℤ) b c d j := ⟨hpa.1, hpb.1⟩
      have hj2 : hAdmissible (a : ℤ) b c d (j + 2) := ⟨hpa.2, hpb.2⟩
      have ha : 0 < a := by
        by_contra hn
        have ha0 : a = 0 := by omega
        subst a
        rcases hpa.1 with ⟨h0, hd, hj0, h1, h2, h3, hp⟩
        rcases hpa.2 with ⟨h0', hd', hj0', h1', h2', h3', hp'⟩
        omega
      have hb : 0 < b := by
        by_contra hn
        have hb0 : b = 0 := by omega
        subst b
        rcases hpb.1 with ⟨h0, hc, hj0, h1, h2, h3, hp⟩
        rcases hpb.2 with ⟨h0', hc', hj0', h1', h2', h3', hp'⟩
        omega
      exact off_horizontal_upper_valid_aux a b c d j ha hb hj hj2
    · rw [off_tet_upper_zero_aux (b : ℤ) c j hpb, Lp2, if_neg]
      · simp
      · rintro ⟨hj, hj2⟩
        exact hpb ⟨hj.2, hj2.2⟩
  · rw [off_tet_upper_zero_aux (a : ℤ) d j hpa, Lp2, if_neg]
    · simp
    · rintro ⟨hj, hj2⟩
      exact hpa ⟨hj.1, hj2.1⟩

/-- Lower neighboring scalar value, again with zero extensions. -/
private lemma off_horizontal_lower_scalar_aux (a b c d j : ℕ) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (j : ℤ) (j + 2) *
      (tetSum (a : ℤ) a j (j + 2) d 2 * tetSum (b : ℤ) b j (j + 2) c 2) =
        Lm2 a b c d ((j : ℤ) + 2) := by
  have hjm : (j : ℤ) + 2 - 2 = (j : ℤ) := by ring
  by_cases hpa : Admissible (a : ℤ) d j ∧ Admissible (a : ℤ) d (j + 2)
  · by_cases hpb : Admissible (b : ℤ) c j ∧ Admissible (b : ℤ) c (j + 2)
    · have hj : hAdmissible (a : ℤ) b c d j := ⟨hpa.1, hpb.1⟩
      have hj2 : hAdmissible (a : ℤ) b c d (j + 2) := ⟨hpa.2, hpb.2⟩
      have ha : 0 < a := by
        by_contra hn
        have ha0 : a = 0 := by omega
        subst a
        rcases hpa.1 with ⟨h0, hd, hj0, h1, h2, h3, hp⟩
        rcases hpa.2 with ⟨h0', hd', hj0', h1', h2', h3', hp'⟩
        omega
      have hb : 0 < b := by
        by_contra hn
        have hb0 : b = 0 := by omega
        subst b
        rcases hpb.1 with ⟨h0, hc, hj0, h1, h2, h3, hp⟩
        rcases hpb.2 with ⟨h0', hc', hj0', h1', h2', h3', hp'⟩
        omega
      exact off_horizontal_lower_valid_aux a b c d j ha hb hj hj2
    · rw [off_tet_lower_zero_aux (b : ℤ) c j hpb, Lm2, if_neg]
      · simp
      · rintro ⟨hj2, hj⟩
        apply hpb
        have hj' : hAdmissible (a : ℤ) b c d j := by simpa only [hjm] using hj
        exact ⟨hj'.2, hj2.2⟩
  · rw [off_tet_lower_zero_aux (a : ℤ) d j hpa, Lm2, if_neg]
    · simp
    · rintro ⟨hj2, hj⟩
      apply hpa
      have hj' : hAdmissible (a : ℤ) b c d j := by simpa only [hjm] using hj
      exact ⟨hj'.1, hj2.1⟩
private lemma matrix_diag (a b c d j : ℤ) :
    L a b c d j j = diagonalEntry a b c d j := by
  simp [L, diagonalEntry]

private lemma matrix_upper (a b c d j : ℤ) :
    L a b c d j (j + 2) = Lp2 a b c d j := by
  have hn : j ≠ j + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (show j + 2 = j + 2 ∨ j = j + 2 + 2 from Or.inl rfl)]
  dsimp only
  rw [min_eq_left (show j ≤ j + 2 by omega), max_eq_right (show j ≤ j + 2 by omega)]
  rfl

private lemma matrix_lower (a b c d j : ℤ) :
    L a b c d j (j - 2) = Lm2 a b c d j := by
  have hn : j ≠ j - 2 := by omega
  have he : j = j - 2 + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (Or.inr he : j - 2 = j + 2 ∨ j = j - 2 + 2)]
  dsimp only
  rw [min_eq_right (show j - 2 ≤ j by omega), max_eq_left (show j - 2 ≤ j by omega)]
  by_cases hj : hAdmissible a b c d j <;>
    by_cases hm : hAdmissible a b c d (j - 2) <;>
    simp only [Lm2, hj, hm, and_self, true_and, false_and,
      and_false, and_true, if_true, if_false] <;> rfl


lemma theta_swap_total (a b c : ℤ) : θ a b c = θ a c b := by
  have hadm : Admissible a b c ↔ Admissible a c b :=
    ⟨adm_swap_right_aux, adm_swap_right_aux⟩
  by_cases h : Admissible a b c
  · have hc := hadm.mp h
    simp [θ, h, hc, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · rw [θ, if_neg h, θ, if_neg]
    exact fun hc => h (hadm.mpr hc)

lemma tet_swap (a r s k t : ℤ) : tetSum a a r s k t = tetSum a a s r k t :=
  off_tet_swap_cd_aux a r s k t

lemma all_entries (a b c d j k : ℕ) :
    ⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭ / θ 2 (k : ℤ) j *
      (tetSum (a : ℤ) a k j d 2 * tetSum (b : ℤ) b k j c 2) = L a b c d j k := by
  rw [theta_swap_total 2 (k : ℤ) (j : ℤ)]
  by_cases he : k = j
  · subst k
    rw [matrix_diag]
    exact horizontal_diag_scalar_aux a b c d j
  by_cases hp : k = j + 2
  · subst k
    rw [show (↑(j + 2) : ℤ) = (j : ℤ) + 2 by omega, matrix_upper]
    exact off_horizontal_upper_scalar_aux a b c d j
  by_cases hm : j = k + 2
  · subst j
    rw [show (↑(k + 2) : ℤ) = (k : ℤ) + 2 by omega]
    have heq : L a b c d ((k : ℤ) + 2) k = Lm2 a b c d ((k : ℤ) + 2) := by
      simpa using matrix_lower a b c d ((k : ℤ) + 2)
    rw [heq]
    have h := off_horizontal_lower_scalar_aux a b c d k
    rw [theta_swap_total 2 ((k : ℤ) + 2) (k : ℤ)]
    simpa using h
  have hc : ¬ Admissible (k : ℤ) j 2 := by
    intro h; dsimp [Admissible] at h; omega
  have hz : tetSum (a : ℤ) a k j d 2 = 0 := by
    rw [tetSum, if_neg]
    rintro ⟨_, hv⟩
    exact hc hv.2
  rw [hz]
  simp only [zero_mul, mul_zero]
  symm
  simp [L, he, hp, hm, show (k : ℤ) ≠ (j : ℤ) + 2 by omega,
    show (j : ℤ) ≠ (k : ℤ) + 2 by omega, show (j : ℤ) ≠ k by omega]

end MatrixScalars
end QuantumSixJ.Network

namespace QuantumSixJ.Network
section MatrixAssembly
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]

private lemma leftTet_identification (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (hSeed : TetSeed W) (a d j k : ℕ) :
    MatrixTriangle.leftTet S W a d j k = W.tet a a k j d 2 := by
  rw [leftTet_swapped S W hW]
  simp only [hSeed.tet_two]
  rw [MatrixScalars.tet_swap a j k d 2]

private lemma matrix_factorization (S : SuQ2Data C) (W : Vertex S)
    (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W)
    (a b c d j k : ℕ) :
    W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      (ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) / ι (θ (2 : ℤ) k j)) •
        (W.tet a a k j d 2 ≫ W.tet b b k j c 2) := by
  rw [MatrixTriangle.factorization S W hS hW,
    leftTet_identification S W hW hSeed, rightTet_identification S W hS hW]

private lemma numerical_matrix (S : SuQ2Data C) (W : Vertex S)
    (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W)
    (a b c d j k : ℕ) :
    W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
      ι (L a b c d j k) • 𝟙 (𝟙_ C) := by
  rw [matrix_factorization S W hS hW hSeed, hSeed.tet_two, hSeed.tet_two]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
  have h := congrArg (fun t : Scalar => ι t • 𝟙 (𝟙_ C))
    (MatrixScalars.all_entries a b c d j k)
  simp only [map_mul, map_div₀] at h
  convert h using 1
  · simp only [map_mul]
    ring

end MatrixAssembly
end QuantumSixJ.Network
open QuantumSixJ.Network
theorem solution {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W) :
    (∀ a d j k : ℕ,
      (W.vertexUp a k d ⊗≫ (W.split a a 2 ▷ (S.V k ⊗ S.V d)) ⊗≫
        (S.V a ◁ (W.fuse 2 k j ▷ S.V d)) ⊗≫ W.vertex a j d) =
          W.tet a a k j d 2) ∧
    (∀ b c j k : ℕ,
      let q : S.V 2 ⊗ S.V k ⟶ S.V j :=
        (S.V 2 ◁ W.split k b c) ⊗≫ (W.fuse 2 b b ▷ S.V c) ≫ W.fuse b c j
      (S.cup j ≫ ((W.split j 2 k ≫ q) ▷ S.V j) ≫ S.cap j) =
        W.tet b b k j c 2) ∧
    (∀ a b c d j k : ℕ,
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
        (ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) / ι (θ (2 : ℤ) k j)) •
          (W.tet a a k j d 2 ≫ W.tet b b k j c 2)) ∧
    (∀ a b c d j k : ℕ, ¬ Admissible (2 : ℤ) k j →
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j = 0) ∧
    (∀ a b c d j k : ℕ,
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
        ι (L a b c d j k) • 𝟙 (𝟙_ C)) := by
  refine ⟨?_, ?_, matrix_factorization S W hS hW hSeed,
    MatrixTriangle.entry_zero S W hS hW, numerical_matrix S W hS hW hSeed⟩
  · intro a d j k
    exact leftTet_identification S W hW hSeed a d j k
  · intro b c j k
    exact rightTet_identification S W hS hW b c j k
