-- Prove2me | solution 1 for RegMatroidXC.Main.proposition_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:16:55.486121+00:00
-- url     : https://prove2.me/submissions/c2521657-ccb0-4036-be2c-4b32bf47aa6a

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
open ExtensionComplexity.TSP

namespace RMXCAux

open Matrix

/-- Flexible form of an extended formulation: variables, equations and inequalities indexed by
arbitrary finite types, given by linear maps. -/
theorem isEF_of_linear {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (r : ℕ)
    {K L J : Type*} [Fintype K] [Fintype L] [Fintype J] (hJ : Fintype.card J ≤ r)
    (A : (ι → ℝ) →ₗ[ℝ] (L → ℝ)) (B : (K → ℝ) →ₗ[ℝ] (L → ℝ)) (b : L → ℝ)
    (C : (ι → ℝ) →ₗ[ℝ] (J → ℝ)) (D : (K → ℝ) →ₗ[ℝ] (J → ℝ)) (c : J → ℝ)
    (h : ∀ x, x ∈ P ↔ ∃ y, A x + B y = b ∧ C x + D y ≤ c) : IsEFOfSize P r := by
  classical
  -- padded inequality index
  let J' := J ⊕ Fin (r - Fintype.card J)
  have hcard : Fintype.card J' = r := by
    simp only [J', Fintype.card_sum, Fintype.card_fin]; omega
  let eJ : J' ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let eK : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let eL : L ≃ Fin (Fintype.card L) := Fintype.equivFin L
  -- linear maps
  let C' : (ι → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun x => Sum.elim (C x) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let D' : (K → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun y => Sum.elim (D y) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let c' : J' → ℝ := Sum.elim c 0
  have hle : ∀ x y, (C' x + D' y ≤ c') ↔ (C x + D y ≤ c) := by
    intro x y
    constructor
    · intro hh j; have := hh (Sum.inl j); simpa [C', D', c'] using this
    · intro hh j; cases j with
      | inl j => simpa [C', D', c'] using hh j
      | inr j => simp [C', D', c']
  let fK : (Fin (Fintype.card K) → ℝ) →ₗ[ℝ] (K → ℝ) := LinearMap.funLeft ℝ ℝ eK
  let fL : (L → ℝ) →ₗ[ℝ] (Fin (Fintype.card L) → ℝ) := LinearMap.funLeft ℝ ℝ eL.symm
  let fJ : (J' → ℝ) →ₗ[ℝ] (Fin r → ℝ) := LinearMap.funLeft ℝ ℝ eJ.symm
  refine ⟨Fintype.card K, Fintype.card L, LinearMap.toMatrix' (fL ∘ₗ A),
    LinearMap.toMatrix' (fL ∘ₗ B ∘ₗ fK), fL b, LinearMap.toMatrix' (fJ ∘ₗ C'),
    LinearMap.toMatrix' (fJ ∘ₗ D' ∘ₗ fK), fJ c', ?_⟩
  intro x
  simp only [LinearMap.toMatrix'_mulVec, LinearMap.coe_comp, Function.comp_apply]
  rw [h]
  have keyL : ∀ u v : L → ℝ, fL u = fL v ↔ u = v := by
    intro u v; constructor
    · intro huv; funext l; have := congrFun huv (eL l); simpa [fL, LinearMap.funLeft] using this
    · intro huv; rw [huv]
  have keyJ : ∀ u v : J' → ℝ, fJ u ≤ fJ v ↔ u ≤ v := by
    intro u v; constructor
    · intro huv l; have := huv (eJ l); simpa [fJ, LinearMap.funLeft] using this
    · intro huv l; simpa [fJ, LinearMap.funLeft] using huv (eJ.symm l)
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨fun i => y (eK.symm i), ?_, ?_⟩
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyL]; exact h1
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyJ, hle]; exact h2
  · rintro ⟨y', h1, h2⟩
    refine ⟨fK y', ?_, ?_⟩
    · rw [← map_add, keyL] at h1; exact h1
    · rw [← map_add, keyJ, hle] at h2; exact h2

end RMXCAux

namespace RMXCAux

open Matrix

/-- The projection of the solution set of a linear system is convex. -/
theorem convex_of_linear {ι K L J : Type*}
    (A : (ι → ℝ) →ₗ[ℝ] (L → ℝ)) (B : (K → ℝ) →ₗ[ℝ] (L → ℝ)) (b : L → ℝ)
    (C : (ι → ℝ) →ₗ[ℝ] (J → ℝ)) (D : (K → ℝ) →ₗ[ℝ] (J → ℝ)) (c : J → ℝ) :
    Convex ℝ {x | ∃ y, A x + B y = b ∧ C x + D y ≤ c} := by
  rintro x1 ⟨y1, h1, h1'⟩ x2 ⟨y2, h2, h2'⟩ a1 a2 ha1 ha2 ha
  refine ⟨a1 • y1 + a2 • y2, ?_, ?_⟩
  · have : A (a1 • x1 + a2 • x2) + B (a1 • y1 + a2 • y2) =
        a1 • (A x1 + B y1) + a2 • (A x2 + B y2) := by
      simp only [map_add, map_smul, smul_add]; abel
    rw [this, h1, h2, ← add_smul, ha, one_smul]
  · have : C (a1 • x1 + a2 • x2) + D (a1 • y1 + a2 • y2) =
        a1 • (C x1 + D y1) + a2 • (C x2 + D y2) := by
      simp only [map_add, map_smul, smul_add]; abel
    rw [this]
    calc a1 • (C x1 + D y1) + a2 • (C x2 + D y2) ≤ a1 • c + a2 • c :=
          add_le_add (smul_le_smul_of_nonneg_left h1' ha1) (smul_le_smul_of_nonneg_left h2' ha2)
      _ = c := by rw [← add_smul, ha, one_smul]

/-- Homogenization of an extended formulation of a nontrivial polytope. -/
theorem hom_facts {ι : Type} [Fintype ι] (P : Set (ι → ℝ)) (hP : IsPolytope P)
    (hnt : P.Nontrivial) {kk p r : ℕ} (E : Matrix (Fin p) ι ℝ) (F : Matrix (Fin p) (Fin kk) ℝ)
    (g : Fin p → ℝ) (G : Matrix (Fin r) ι ℝ) (H : Matrix (Fin r) (Fin kk) ℝ) (h : Fin r → ℝ)
    (hEF : ∀ x, x ∈ P ↔ ∃ y, E *ᵥ x + F *ᵥ y = g ∧ G *ᵥ x + H *ᵥ y ≤ h)
    (x : ι → ℝ) (y : Fin kk → ℝ) (l : ℝ)
    (hQ : E *ᵥ x + F *ᵥ y = l • g ∧ G *ᵥ x + H *ᵥ y ≤ l • h) :
    0 ≤ l ∧ (l = 0 → x = 0) ∧ (0 < l → l⁻¹ • x ∈ P) := by
  -- the homogenized system
  let Q : (ι → ℝ) → (Fin kk → ℝ) → ℝ → Prop := fun x y l =>
    E *ᵥ x + F *ᵥ y = l • g ∧ G *ᵥ x + H *ᵥ y ≤ l • h
  have hscale : ∀ x y l (t : ℝ), 0 ≤ t → Q x y l → Q (t • x) (t • y) (t * l) := by
    rintro x y l t ht ⟨q1, q2⟩
    refine ⟨?_, ?_⟩
    · rw [mulVec_smul, mulVec_smul, ← smul_add, q1, smul_smul]
    · rw [mulVec_smul, mulVec_smul, ← smul_add, mul_smul]
      exact smul_le_smul_of_nonneg_left q2 ht
  have hadd : ∀ x y l x' y' l', Q x y l → Q x' y' l' → Q (x + x') (y + y') (l + l') := by
    rintro x y l x' y' l' ⟨q1, q2⟩ ⟨q1', q2'⟩
    refine ⟨?_, ?_⟩
    · rw [mulVec_add, mulVec_add, add_smul, ← q1, ← q1']; abel
    · rw [mulVec_add, mulVec_add, add_smul]
      have := add_le_add q2 q2'
      calc G *ᵥ x + G *ᵥ x' + (H *ᵥ y + H *ᵥ y') = (G *ᵥ x + H *ᵥ y) + (G *ᵥ x' + H *ᵥ y') := by
            abel
        _ ≤ l • h + l' • h := this
  have hone : ∀ x y, Q x y 1 → x ∈ P := by
    intro x y hq; rw [hEF]; refine ⟨y, ?_, ?_⟩
    · simpa using hq.1
    · simpa using hq.2
  have hmem : ∀ x ∈ P, ∃ y, Q x y 1 := by
    intro x hx; rw [hEF] at hx; obtain ⟨y, h1, h2⟩ := hx
    exact ⟨y, by simpa using h1, by simpa using h2⟩
  -- boundedness
  obtain ⟨V, hV⟩ := hP
  have hbdd : Bornology.IsBounded P := by
    rw [hV, isBounded_convexHull]; exact (V.finite_toSet).isBounded
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
  -- recession directions vanish
  have hzero : ∀ x y, Q x y 0 → x = 0 := by
    intro x y hq
    obtain ⟨x0, hx0⟩ := hnt.nonempty
    obtain ⟨y0, hy0⟩ := hmem x0 hx0
    by_contra hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    set t : ℝ := (R + ‖x0‖ + 1) / ‖x‖ with ht
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR x0 hx0)
    have htnn : 0 ≤ t := by positivity
    have hq' := hadd _ _ _ _ _ _ hy0 (hscale x y 0 t htnn hq)
    rw [mul_zero, add_zero] at hq'
    have hin := hR _ (hone _ _ hq')
    have h1 : ‖t • x‖ ≤ ‖x0 + t • x‖ + ‖x0‖ := by
      have := norm_sub_le (x0 + t • x) x0
      simpa [add_sub_cancel_left] using this
    rw [norm_smul, Real.norm_of_nonneg htnn, ht, div_mul_cancel₀ _ hnx.ne'] at h1
    linarith
  -- negative multiplier impossible
  have hneg : ∀ x y l, Q x y l → 0 ≤ l := by
    intro x y l hq
    by_contra hl
    push Not at hl
    have hq1 := hscale x y l (-l)⁻¹ (inv_nonneg.2 (by linarith)) hq
    have hl1 : (-l)⁻¹ * l = -1 := by rw [← neg_inv, neg_mul, inv_mul_cancel₀ hl.ne]
    rw [hl1] at hq1
    have key : ∀ z ∈ P, z = -((-l)⁻¹ • x) := by
      intro z hz
      obtain ⟨yz, hyz⟩ := hmem z hz
      have hs := hadd _ _ _ _ _ _ hyz hq1
      rw [show (1:ℝ) + -1 = 0 by norm_num] at hs
      have := hzero _ _ hs
      exact eq_neg_of_add_eq_zero_left this
    obtain ⟨z1, hz1, z2, hz2, hne⟩ := hnt
    exact hne ((key z1 hz1).trans (key z2 hz2).symm)
  refine ⟨hneg x y l hQ, fun hl => hzero x y (hl ▸ hQ), fun hl => ?_⟩
  have := hscale x y l l⁻¹ (inv_nonneg.2 hl.le) hQ
  rw [inv_mul_cancel₀ hl.ne'] at this
  exact hone _ _ this

theorem prop12_aux {ι : Type} [Fintype ι] (k : ℕ) (P : Fin k → Set (ι → ℝ))
    (hP : ∀ i, IsPolytope (P i)) (hdim : ∀ i, (P i).Nontrivial)
    (r : Fin k → ℕ) (hr : ∀ i, IsEFOfSize (P i) (r i)) :
    ∃ s : ℕ, IsEFOfSize (convexHull ℝ (⋃ i, P i)) s ∧ s ≤ ∑ i, r i := by
  classical
  choose kk pp E F g G H h hEF using hr
  let K := Σ i : Fin k, ι ⊕ (Fin (kk i) ⊕ Unit)
  let Xf : (K → ℝ) → (i : Fin k) → (ι → ℝ) := fun v i e => v ⟨i, Sum.inl e⟩
  let Yf : (K → ℝ) → (i : Fin k) → (Fin (kk i) → ℝ) := fun v i j => v ⟨i, Sum.inr (Sum.inl j)⟩
  let lf : (K → ℝ) → Fin k → ℝ := fun v i => v ⟨i, Sum.inr (Sum.inr ())⟩
  let L := ι ⊕ (Unit ⊕ Σ i : Fin k, Fin (pp i))
  let J := Σ i : Fin k, Fin (r i)
  let A : (ι → ℝ) →ₗ[ℝ] (L → ℝ) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext j; rcases j with j | j | j <;> simp
      map_smul' := by intro a x; ext j; rcases j with j | j | j <;> simp }
  let B : (K → ℝ) →ₗ[ℝ] (L → ℝ) :=
    { toFun := fun v => Sum.elim (fun e => -∑ i, Xf v i e)
        (Sum.elim (fun _ => ∑ i, lf v i)
          (fun ij => (E ij.1 *ᵥ Xf v ij.1 + F ij.1 *ᵥ Yf v ij.1 - lf v ij.1 • g ij.1) ij.2))
      map_add' := by
        intro v w; ext j; rcases j with j | j | ⟨i, j⟩
        · simp [Xf, Finset.sum_add_distrib]; ring
        · simp [lf, Finset.sum_add_distrib]
        · have hX : Xf (v + w) i = Xf v i + Xf w i := rfl
          have hY : Yf (v + w) i = Yf v i + Yf w i := rfl
          have hl : lf (v + w) i = lf v i + lf w i := rfl
          simp only [Sum.elim_inr, Pi.add_apply, hX, hY, hl, mulVec_add, Pi.sub_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
      map_smul' := by
        intro a v; ext j; rcases j with j | j | ⟨i, j⟩
        · simp [Xf, Finset.mul_sum]
        · simp [lf, Finset.mul_sum]
        · have hX : Xf (a • v) i = a • Xf v i := rfl
          have hY : Yf (a • v) i = a • Yf v i := rfl
          have hl : lf (a • v) i = a * lf v i := rfl
          simp only [Sum.elim_inr, Pi.smul_apply, hX, hY, hl, mulVec_smul, Pi.add_apply,
            Pi.sub_apply, smul_eq_mul, RingHom.id_apply]
          ring }
  let b : L → ℝ := Sum.elim 0 (Sum.elim 1 0)
  let C : (ι → ℝ) →ₗ[ℝ] (J → ℝ) := 0
  let D : (K → ℝ) →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun v ij =>
        (G ij.1 *ᵥ Xf v ij.1 + H ij.1 *ᵥ Yf v ij.1 - lf v ij.1 • h ij.1) ij.2
      map_add' := by
        intro v w; ext ⟨i, j⟩
        have hX : Xf (v + w) i = Xf v i + Xf w i := rfl
        have hY : Yf (v + w) i = Yf v i + Yf w i := rfl
        have hl : lf (v + w) i = lf v i + lf w i := rfl
        simp only [Pi.add_apply, hX, hY, hl, mulVec_add, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      map_smul' := by
        intro a v; ext ⟨i, j⟩
        have hX : Xf (a • v) i = a • Xf v i := rfl
        have hY : Yf (a • v) i = a • Yf v i := rfl
        have hl : lf (a • v) i = a * lf v i := rfl
        simp only [Pi.smul_apply, hX, hY, hl, mulVec_smul, Pi.add_apply, Pi.sub_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }
  let Q : (i : Fin k) → (ι → ℝ) → (Fin (kk i) → ℝ) → ℝ → Prop := fun i x y l =>
    E i *ᵥ x + F i *ᵥ y = l • g i ∧ G i *ᵥ x + H i *ᵥ y ≤ l • h i
  have hsys : ∀ x v, (A x + B v = b ∧ C x + D v ≤ 0) ↔
      ((∀ e, x e = ∑ i, Xf v i e) ∧ ∑ i, lf v i = 1 ∧ ∀ i, Q i (Xf v i) (Yf v i) (lf v i)) := by
    intro x v
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun e => ?_, ?_, fun i => ⟨?_, ?_⟩⟩
      · have := congrFun h1 (Sum.inl e)
        simp [A, B, b] at this; linarith
      · have := congrFun h1 (Sum.inr (Sum.inl ()))
        simpa [A, B, b] using this
      · funext j
        have := congrFun h1 (Sum.inr (Sum.inr ⟨i, j⟩))
        simp only [A, B, b, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Sum.elim_inr,
          Pi.zero_apply, zero_add, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        linarith
      · intro j
        have := h2 ⟨i, j⟩
        simp only [C, D, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, LinearMap.zero_apply,
          Pi.zero_apply, zero_add, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        linarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_⟩
      · funext j; rcases j with e | u | ⟨i, j⟩
        · simp [A, B, b, h1 e]
        · simpa [A, B, b] using h2
        · have := congrFun (h3 i).1 j
          simp only [A, B, b, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Sum.elim_inr,
            Pi.zero_apply, zero_add, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
          linarith
      · rintro ⟨i, j⟩
        have := (h3 i).2 j
        simp only [C, D, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, LinearMap.zero_apply,
          Pi.zero_apply, zero_add, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        linarith
  have hcard : Fintype.card J = ∑ i, r i := by simp [J]
  refine ⟨Fintype.card J, isEF_of_linear _ _ le_rfl A B b C D 0 ?_, hcard.le⟩
  intro x
  constructor
  · -- convex hull ⊆ feasible projections
    intro hx
    have hconv := convex_of_linear A B b C D 0
    have hsub : (⋃ i, P i) ⊆ {x | ∃ y, A x + B y = b ∧ C x + D y ≤ 0} := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      obtain ⟨y, hy1, hy2⟩ := (hEF i z).1 hi
      let vi : ι ⊕ (Fin (kk i) ⊕ Unit) → ℝ := Sum.elim z (Sum.elim y (fun _ => 1))
      let v : K → ℝ := fun s =>
        (Pi.single (M := fun j => ι ⊕ (Fin (kk j) ⊕ Unit) → ℝ) i vi) s.1 s.2
      refine ⟨v, (hsys z v).2 ⟨fun e => ?_, ?_, fun j => ?_⟩⟩
      · rw [Finset.sum_eq_single i]
        · simp [Xf, v, vi]
        · intro j _ hj; simp [Xf, v, Pi.single_eq_of_ne hj]
        · simp
      · rw [Finset.sum_eq_single i]
        · simp [lf, v, vi]
        · intro j _ hj; simp [lf, v, Pi.single_eq_of_ne hj]
        · simp
      · by_cases hj : j = i
        · subst hj
          have e1 : Xf v j = z := by funext e; simp [Xf, v, vi]
          have e2 : Yf v j = y := by funext e; simp [Yf, v, vi]
          have e3 : lf v j = 1 := by simp [lf, v, vi]
          rw [e1, e2, e3]
          exact ⟨by simpa using hy1, by simpa using hy2⟩
        · have e1 : Xf v j = 0 := by funext e; simp [Xf, v, Pi.single_eq_of_ne hj]
          have e2 : Yf v j = 0 := by funext e; simp [Yf, v, Pi.single_eq_of_ne hj]
          have e3 : lf v j = 0 := by simp [lf, v, Pi.single_eq_of_ne hj]
          rw [e1, e2, e3]
          refine ⟨by simp, by simp⟩
    exact convexHull_min hsub hconv hx
  · rintro ⟨v, hv⟩
    obtain ⟨h1, h2, h3⟩ := (hsys x v).1 hv
    have hf := fun i => hom_facts (P i) (hP i) (hdim i) (E i) (F i) (g i) (G i) (H i) (h i)
      (hEF i) (Xf v i) (Yf v i) (lf v i) (h3 i)
    have hpt : ∀ i, ∃ p ∈ P i, Xf v i = lf v i • p := by
      intro i
      rcases (hf i).1.lt_or_eq with hl | hl
      · refine ⟨(lf v i)⁻¹ • Xf v i, (hf i).2.2 hl, ?_⟩
        rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
      · obtain ⟨p, hp⟩ := (hdim i).nonempty
        refine ⟨p, hp, ?_⟩
        rw [(hf i).2.1 hl.symm, ← hl, zero_smul]
    choose p hp hXp using hpt
    refine mem_convexHull_of_exists_fintype (fun i => lf v i) p (fun i => (hf i).1) h2
      (fun i => Set.mem_iUnion.2 ⟨i, hp i⟩) ?_
    funext e
    rw [h1 e]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hXp i]

end RMXCAux

theorem solution {ι : Type} [Fintype ι] (k : ℕ) (P : Fin k → Set (ι → ℝ))
    (hP : ∀ i, IsPolytope (P i)) (hdim : ∀ i, (P i).Nontrivial)
    (r : Fin k → ℕ) (hr : ∀ i, IsEFOfSize (P i) (r i)) :
    ∃ s : ℕ, IsEFOfSize (convexHull ℝ (⋃ i, P i)) s ∧ s ≤ ∑ i, r i :=
  RMXCAux.prop12_aux k P hP hdim r hr
