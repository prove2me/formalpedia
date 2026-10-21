-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_localProcessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:16:11.435305+00:00
-- url     : https://prove2.me/submissions/109d5bac-147d-4c9a-a447-57bb84368a68

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

section g59d_norms
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open QAlgorithms
theorem g59d_spec_nonneg {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (X : Matrix m n ℂ) :
    0 ≤ specNorm X := by
  unfold specNorm
  exact @norm_nonneg _ (@NormedAddCommGroup.toSeminormedAddCommGroup _
    Matrix.instL2OpNormedAddCommGroup).toSeminormedAddGroup X

theorem g59d_spec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {ι : Type} [Fintype ι]
    (H : ι → Matrix n m ℂ) (hH : ∑ i, H i * (H i)ᴴ = 1) (X : Matrix m m ℂ) (hX : X.PosSemidef) :
    specNorm (∑ i, H i * X * (H i)ᴴ) ≤ specNorm X := by
  have hXn := g59d_spec_nonneg X
  unfold specNorm at hXn ⊢
  have h0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  have h1 : X ≤ algebraMap ℝ (Matrix m m ℂ) ‖X‖ := IsSelfAdjoint.le_algebraMap_norm_self (.of_nonneg h0)
  have h2 : (0 : Matrix n n ℂ) ≤ ∑ i, H i * X * (H i)ᴴ := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same (H i))
  have h3 : ∑ i, H i * X * (H i)ᴴ ≤ algebraMap ℝ (Matrix n n ℂ) ‖X‖ := by
    rw [Matrix.le_iff] at h1 ⊢
    have e : algebraMap ℝ (Matrix n n ℂ) ‖X‖ - ∑ i, H i * X * (H i)ᴴ =
        ∑ i, H i * (algebraMap ℝ (Matrix m m ℂ) ‖X‖ - X) * (H i)ᴴ := by
      simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul,
        Finset.sum_sub_distrib, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [← Finset.smul_sum, hH]
    rw [e]
    exact Matrix.posSemidef_sum _ (fun i _ => h1.mul_mul_conjTranspose_same (H i))
  have := CStarAlgebra.norm_le_norm_of_nonneg_of_le h2 h3
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim (∑ i, H i * X * (H i)ᴴ) 0, norm_zero]; exact hXn
  · rw [norm_algebraMap', Real.norm_eq_abs] at this
    exact this.trans_eq (abs_of_nonneg hXn)

end g59d_norms


noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

theorem g59d_tensor_single {A B C D : Type} [Fintype A] [Fintype B]
    (E : Superop A C) (F : Superop B D) (a aa : A) (b bb : B) (p q : C × D) :
    tensorAction E F (Matrix.single (a, b) (aa, bb) 1) p q =
      E (Matrix.single a aa 1) p.1 q.1 * F (Matrix.single b bb 1) p.2 q.2 := by
  simp only [tensorAction]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single aa (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single b (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single bb (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  simp [Matrix.single_apply]

theorem g59d_kraus_apply {ι I J : Type} [Fintype ι] [Fintype I]
    (K : ι → Matrix J I ℂ) (Y : Matrix I I ℂ) (u v : J) :
    krausApply K Y u v = ∑ i, ∑ x, ∑ y, K i u x * Y x y * star (K i v y) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

theorem g59d_kraus_single {ι I J : Type} [Fintype ι] [Fintype I] [DecidableEq I]
    (K : ι → Matrix J I ℂ) (a aa : I) (u v : J) :
    krausApply K (Matrix.single a aa 1) u v = ∑ i, K i u a * star (K i v aa) := by
  rw [g59d_kraus_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_eq_single a (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single aa (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  simp

theorem g59d_kraus_lin {ι I J : Type} [Fintype ι] [Fintype I] [DecidableEq I]
    (K : ι → Matrix J I ℂ) (Y : Matrix I I ℂ) (u v : J) :
    krausApply K Y u v = ∑ x, ∑ y, Y x y * krausApply K (Matrix.single x y 1) u v := by
  rw [g59d_kraus_apply]
  simp_rw [g59d_kraus_single, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem g59d_tensor_kraus {A B C D : Type} [Fintype A] [Fintype B] {ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]
    (P : ι1 → Matrix C A ℂ) (Q : ι2 → Matrix D B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    tensorAction (krausApply P) (krausApply Q) X =
      krausApply (fun ij : ι1 × ι2 => Matrix.kronecker (P ij.1) (Q ij.2)) X := by
  ext p q
  simp only [tensorAction, g59d_kraus_single]
  rw [g59d_kraus_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum,
    Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.2.2.2, x.2.2.2.2.1, x.1, x.2.2.1, x.2.1, x.2.2.2.1)
      invFun := fun y => (y.2.2.1, y.2.2.2.2.1, y.2.2.2.1, y.2.2.2.2.2, y.2.1, y.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk, star_mul']
  ring

theorem g59d_kraus_comp {I I' O O' : Type} [Fintype I] [Fintype I'] [Fintype O]
    {ιX ιM ιY : Type} [Fintype ιX] [Fintype ιM] [Fintype ιY]
    (X : ιX → Matrix I I' ℂ) (Mk : ιM → Matrix O I ℂ) (Y : ιY → Matrix O' O ℂ) (ρ : Matrix I' I' ℂ) :
    krausApply Y (krausApply Mk (krausApply X ρ)) =
      krausApply (fun t : ιY × ιM × ιX => Y t.1 * Mk t.2.1 * X t.2.2) ρ := by
  simp only [krausApply, Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem g59d_choi_kraus {ι I O : Type} [Fintype ι] [Fintype I] [DecidableEq I]
    (Z : ι → Matrix O I ℂ) (p q : I × O) :
    choi (krausApply Z) p q = ∑ t, Z t p.2 p.1 * star (Z t q.2 q.1) := by
  simp only [choi, g59d_kraus_single]

theorem g59d_choi_sandwich {I I' O O' : Type} [Fintype I] [Fintype I'] [Fintype O] [Fintype O']
    [DecidableEq I] [DecidableEq I']
    {ιX ιM ιY : Type} [Fintype ιX] [Fintype ιM] [Fintype ιY]
    (X : ιX → Matrix I I' ℂ) (Mk : ιM → Matrix O I ℂ) (Y : ιY → Matrix O' O ℂ) :
    choi (fun ρ => krausApply Y (krausApply Mk (krausApply X ρ))) =
      ∑ st : ιX × ιY, Matrix.kronecker (X st.1).transpose (Y st.2) * choi (krausApply Mk) *
        (Matrix.kronecker (X st.1).transpose (Y st.2))ᴴ := by
  have e1 : (fun ρ => krausApply Y (krausApply Mk (krausApply X ρ))) =
      krausApply (fun t : ιY × ιM × ιX => Y t.1 * Mk t.2.1 * X t.2.2) := by
    funext ρ; exact g59d_kraus_comp X Mk Y ρ
  have hent : ∀ (s : ιX) (t : ιY) (m : ιM) (p : I' × O'),
      (Y t * Mk m * X s) p.2 p.1 = ∑ u : I × O,
        Matrix.kronecker (X s).transpose (Y t) p u * Mk m u.2 u.1 := by
    intro s t m p
    simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun o _ => ?_)
    ring
  have hblk : ∀ (G : Matrix (I' × O') (I × O) ℂ) (p q : I' × O'),
      (G * choi (krausApply Mk) * Gᴴ) p q =
        ∑ m, (∑ u, G p u * Mk m u.2 u.1) * star (∑ v, G q v * Mk m v.2 v.1) := by
    intro G p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g59d_choi_kraus, star_sum,
      Finset.sum_mul, Finset.mul_sum, star_mul']
    simp only [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv
      { toFun := fun x : (I × O) × (I × O) × ιM => (x.2.2, x.1, x.2.1),
        invFun := fun y : ιM × (I × O) × (I × O) => (y.2.1, y.2.2, y.1),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
    simp only [Equiv.coe_fn_mk]
    ring
  rw [e1]
  ext p q
  rw [g59d_choi_kraus, Matrix.sum_apply]
  simp only [hblk]
  simp only [hent]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
      { toFun := fun x : ιY × ιM × ιX => (x.2.2, x.1, x.2.1),
        invFun := fun y : ιX × ιY × ιM => (y.2.1, y.2.2, y.1),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => rfl)

theorem g59d_tp_entry {ι O O' : Type} [Fintype ι] [Fintype O'] [DecidableEq O]
    (Y : ι → Matrix O' O ℂ) (hY : ∑ t, (Y t)ᴴ * Y t = 1) (u v : O) :
    ∑ t, ∑ o, Y t o u * star (Y t o v) = if u = v then 1 else 0 := by
  have := congrFun (congrFun hY v) u
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  rw [show (if u = v then (1:ℂ) else 0) = if v = u then 1 else 0 from by
    by_cases h : u = v <;> simp [h, eq_comm], ← this]
  refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun o _ => ?_))
  ring

theorem g59d_traceOutput_sandwich {I I' O O' : Type} [Fintype I] [Fintype I'] [Fintype O] [Fintype O']
    [DecidableEq O] {ιX ιY : Type} [Fintype ιX] [Fintype ιY]
    (X : ιX → Matrix I I' ℂ) (Y : ιY → Matrix O' O ℂ) (hY : ∑ t, (Y t)ᴴ * Y t = 1)
    (J : Matrix (I × O) (I × O) ℂ) :
    traceOutput (∑ st : ιX × ιY, Matrix.kronecker (X st.1).transpose (Y st.2) * J *
        (Matrix.kronecker (X st.1).transpose (Y st.2))ᴴ) =
      ∑ s, (X s).transpose * traceOutput J * ((X s).transpose)ᴴ := by
  ext i i'
  simp only [traceOutput, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h2 : ∀ u1 u2 v1 v2, ∑ t, ∑ o, X s u1 i * Y t o u2 * J (u1, u2) (v1, v2) *
      star (X s v1 i' * Y t o v2) =
      X s u1 i * J (u1, u2) (v1, v2) * star (X s v1 i') * (if u2 = v2 then 1 else 0) := by
    intro u1 u2 v1 v2
    rw [← g59d_tp_entry Y hY u2 v2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [star_mul']; ring
  calc _ = ∑ u1, ∑ u2, ∑ v1, ∑ v2, ∑ t, ∑ o, X s u1 i * Y t o u2 * J (u1, u2) (v1, v2) *
      star (X s v1 i' * Y t o v2) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        simp only [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv
          { toFun := fun x : O' × ιY × I × O × I × O => (x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.1, x.1)
            invFun := fun y : I × O × I × O × ιY × O' => (y.2.2.2.2.2, y.2.2.2.2.1, y.2.2.1, y.2.2.2.1, y.1, y.2.1)
            left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => rfl)
    _ = ∑ u1, ∑ u2, ∑ v1, ∑ v2, X s u1 i * J (u1, u2) (v1, v2) * star (X s v1 i') *
          (if u2 = v2 then 1 else 0) := by simp only [h2]
    _ = _ := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [Finset.sum_mul, Finset.mul_sum]
        simp only [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv
          { toFun := fun x : I × O × I => (x.2.2, x.1, x.2.1)
            invFun := fun y : I × I × O => (y.2.1, y.2.2, y.1)
            left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => rfl)

theorem g59d_conj_apply {I J : Type} [Fintype I] (G : Matrix J I ℂ) (Z : Matrix I I ℂ) (p q : J) :
    (G * Z * Gᴴ) p q = ∑ x, ∑ y, G p x * Z x y * star (G q y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem g59d_T_conj {A B C D E F K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P0 : Matrix A E ℂ) (Q0 : Matrix B F ℂ) (R0 : Matrix K C ℂ) (T0 : Matrix L D ℂ)
    (Z : Op ((A × B) × (C × D))) :
    transposeBobChoi (Matrix.kronecker (Matrix.kronecker P0 Q0).transpose (Matrix.kronecker R0 T0) * Z *
        (Matrix.kronecker (Matrix.kronecker P0 Q0).transpose (Matrix.kronecker R0 T0))ᴴ) =
      Matrix.kronecker (Matrix.kronecker P0 (Q0.map star)).transpose (Matrix.kronecker R0 (T0.map star)) *
        transposeBobChoi Z *
        (Matrix.kronecker (Matrix.kronecker P0 (Q0.map star)).transpose (Matrix.kronecker R0 (T0.map star)))ᴴ := by
  ext p q
  rw [g59d_conj_apply]
  simp only [transposeBobChoi]
  rw [g59d_conj_apply]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun z : ((A × B) × (C × D)) × ((A × B) × (C × D)) =>
        (((z.1.1.1, z.2.1.2), (z.1.2.1, z.2.2.2)), ((z.2.1.1, z.1.1.2), (z.2.2.1, z.1.2.2)))
      invFun := fun z : ((A × B) × (C × D)) × ((A × B) × (C × D)) =>
        (((z.1.1.1, z.2.1.2), (z.1.2.1, z.2.2.2)), ((z.2.1.1, z.1.1.2), (z.2.2.1, z.1.2.2)))
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun z => ?_)
  simp only [Equiv.coe_fn_mk, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.map_apply, star_mul', star_star]
  ring

def g59d_NS' {A B C D : Type} [Fintype C] (S : Op ((A × B) × (C × D))) : Prop :=
  ∃ W : Matrix (B × D) (B × D) ℂ, ∀ a aa b bb d dd,
    (∑ c, S ((a,b),(c,d)) ((aa,bb),(c,dd))) = if a = aa then W (b,d) (bb,dd) else 0

theorem g59d_NS_pres {A B C D E F K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] [Fintype K] [Fintype L] [DecidableEq E] [DecidableEq C]
    {ι1 ι2 ι3 ι4 : Type} [Fintype ι1] [Fintype ι2] [Fintype ι3] [Fintype ι4]
    (P : ι1 → Matrix A E ℂ) (Q : ι2 → Matrix B F ℂ) (R : ι3 → Matrix K C ℂ) (T : ι4 → Matrix L D ℂ)
    (hP : ∑ i, (P i)ᴴ * P i = 1) (hR : ∑ k, (R k)ᴴ * R k = 1)
    (S : Op ((A × B) × (C × D))) (hS : g59d_NS' S) :
    g59d_NS' (∑ st : (ι1 × ι2) × (ι3 × ι4),
      Matrix.kronecker (Matrix.kronecker (P st.1.1) (Q st.1.2)).transpose
        (Matrix.kronecker (R st.2.1) (T st.2.2)) * S *
      (Matrix.kronecker (Matrix.kronecker (P st.1.1) (Q st.1.2)).transpose
        (Matrix.kronecker (R st.2.1) (T st.2.2)))ᴴ) := by
  obtain ⟨W, hW⟩ := hS
  refine ⟨fun fl fl' => ∑ j, ∑ l0, ∑ b, ∑ d, ∑ b', ∑ d', Q j b fl.1 * T l0 fl.2 d * W (b, d) (b', d') *
    (star (Q j b' fl'.1) * star (T l0 fl'.2 d')), ?_⟩
  intro e e' f f' l l'
  simp only [Matrix.sum_apply, g59d_conj_apply]
  calc _ = ∑ i, ∑ j, ∑ l0, ∑ a, ∑ b, ∑ d, ∑ b', ∑ d', ∑ a', ∑ c, ∑ c', ∑ kk, ∑ k,
      (P i a e * Q j b f * T l0 l d * (star (P i a' e') * star (Q j b' f') * star (T l0 l' d'))) *
        (S ((a,b),(c,d)) ((a',b'),(c',d')) * (R kk k c * star (R kk k c'))) := by
        simp only [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv
          { toFun := fun z : K × ((ι1 × ι2) × (ι3 × ι4)) × ((A × B) × (C × D)) × ((A × B) × (C × D)) =>
              (z.2.1.1.1, z.2.1.1.2, z.2.1.2.2, z.2.2.1.1.1, z.2.2.1.1.2, z.2.2.1.2.2, z.2.2.2.1.2,
                z.2.2.2.2.2, z.2.2.2.1.1, z.2.2.1.2.1, z.2.2.2.2.1, z.2.1.2.1, z.1)
            invFun := fun y => (y.2.2.2.2.2.2.2.2.2.2.2.2, ((y.1, y.2.1), (y.2.2.2.2.2.2.2.2.2.2.2.1, y.2.2.1)),
              ((y.2.2.2.1, y.2.2.2.2.1), (y.2.2.2.2.2.2.2.2.2.1, y.2.2.2.2.2.1)),
              ((y.2.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.1), (y.2.2.2.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.1)))
            left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun z => ?_)
        simp only [Equiv.coe_fn_mk, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
          star_mul']
        ring
    _ = ∑ i, ∑ j, ∑ l0, ∑ a, ∑ b, ∑ d, ∑ b', ∑ d',
      (P i a e * Q j b f * T l0 l d * (star (P i a e') * star (Q j b' f') * star (T l0 l' d'))) *
        W (b, d) (b', d') := by
        simp only [← Finset.mul_sum, g59d_tp_entry R hR, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, hW, Finset.sum_ite_eq']
    _ = ∑ j, ∑ l0, ∑ b, ∑ d, ∑ b', ∑ d', ∑ i, ∑ a,
      (Q j b f * T l0 l d * W (b, d) (b', d') * (star (Q j b' f') * star (T l0 l' d'))) *
        (P i a e * star (P i a e')) := by
        simp only [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv
          { toFun := fun z : ι1 × ι2 × ι4 × A × B × D × B × D =>
              (z.2.1, z.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2, z.1, z.2.2.2.1)
            invFun := fun y : ι2 × ι4 × B × D × B × D × ι1 × A =>
              (y.2.2.2.2.2.2.1, y.1, y.2.1, y.2.2.2.2.2.2.2, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1)
            left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun z => ?_)
        simp only [Equiv.coe_fn_mk]
        ring
    _ = _ := by
        simp only [← Finset.mul_sum, g59d_tp_entry P hP]
        by_cases h : e = e'
        · simp [h]
        · simp [h]

theorem g59d_logExt_mono {x y : EReal} (h : x ≤ y) : logExt x ≤ logExt y := by
  unfold logExt
  by_cases hy : y = ⊤
  · simp [hy]
  have hx : x ≠ ⊤ := fun hx => hy (top_le_iff.mp (hx ▸ h))
  rw [if_neg hx, if_neg hy]
  by_cases hx0 : x ≤ 0
  · rw [if_pos hx0]; exact bot_le
  have hy0 : ¬ y ≤ 0 := fun hy0 => hx0 (h.trans hy0)
  rw [if_neg hx0, if_neg hy0]
  push_neg at hx0
  have hxb : x ≠ ⊥ := ne_bot_of_gt hx0
  have hxr : 0 < x.toReal := by
    have := EReal.toReal_pos hx0 hx
    exact this
  have := EReal.toReal_le_toReal h hxb hy
  exact_mod_cast Real.logb_le_logb_of_le (by norm_num) hxr this

theorem g59d_herm_sum {ι n : Type} [Fintype ι] (f : ι → Matrix n n ℂ) (h : ∀ i, (f i).IsHermitian) :
    (∑ i, f i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem g59d_tB_sum {A B C D : Type} {ι : Type} [Fintype ι] (f : ι → Op ((A × B) × (C × D))) :
    transposeBobChoi (∑ i, f i) = ∑ i, transposeBobChoi (f i) := by
  ext p q; simp [transposeBobChoi, Matrix.sum_apply]

theorem g59d_tB_add {A B C D : Type} (X Y : Op ((A × B) × (C × D))) :
    transposeBobChoi (X + Y) = transposeBobChoi X + transposeBobChoi Y := by
  ext p q; rfl

theorem g59d_tB_sub {A B C D : Type} (X Y : Op ((A × B) × (C × D))) :
    transposeBobChoi (X - Y) = transposeBobChoi X - transposeBobChoi Y := by
  ext p q; rfl

theorem g59d_sum_kron {ι1 ι2 a b c d : Type} [Fintype ι1] [Fintype ι2]
    (X : ι1 → Matrix a b ℂ) (Y : ι2 → Matrix c d ℂ) :
    ∑ ij : ι1 × ι2, Matrix.kronecker (X ij.1) (Y ij.2) = Matrix.kronecker (∑ i, X i) (∑ j, Y j) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

theorem g59d_kron_tp {ι1 ι2 A B E F : Type} [Fintype ι1] [Fintype ι2] [Fintype A] [Fintype B]
    [DecidableEq E] [DecidableEq F]
    (P : ι1 → Matrix A E ℂ) (Q : ι2 → Matrix B F ℂ)
    (hP : ∑ i, (P i)ᴴ * P i = 1) (hQ : ∑ j, (Q j)ᴴ * Q j = 1) :
    ∑ ij : ι1 × ι2, (Matrix.kronecker (P ij.1) (Q ij.2))ᴴ * Matrix.kronecker (P ij.1) (Q ij.2) = 1 := by
  have : ∀ ij : ι1 × ι2, (Matrix.kronecker (P ij.1) (Q ij.2))ᴴ * Matrix.kronecker (P ij.1) (Q ij.2) =
      Matrix.kronecker ((P ij.1)ᴴ * P ij.1) ((Q ij.2)ᴴ * Q ij.2) := by
    intro ij
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [this]
  rw [g59d_sum_kron (fun i => (P i)ᴴ * P i) (fun j => (Q j)ᴴ * Q j), hP, hQ]
  simp only [Matrix.kronecker]
  exact Matrix.one_kronecker_one

theorem g59d_transpose_unital {ι a b : Type} [Fintype ι] [Fintype a] [DecidableEq b]
    (X : ι → Matrix a b ℂ) (hX : ∑ i, (X i)ᴴ * X i = 1) :
    ∑ i, (X i).transpose * ((X i).transpose)ᴴ = 1 := by
  have : ∑ i, (X i).transpose * ((X i).transpose)ᴴ = (∑ i, (X i)ᴴ * X i).transpose := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun o _ => ?_))
    ring
  rw [this, hX, Matrix.transpose_one]

theorem g59d_traceOutput_psd {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (S : Matrix (I × O) (I × O) ℂ) (hS : S.PosSemidef) : (traceOutput S).PosSemidef := by
  have : traceOutput S = ∑ o : O, (Matrix.of fun (i : I) (p : I × O) => if p = (i, o) then (1:ℂ) else 0) * S *
      (Matrix.of fun (i : I) (p : I × O) => if p = (i, o) then (1:ℂ) else 0)ᴴ := by
    ext i j
    simp only [traceOutput, Matrix.sum_apply, g59d_conj_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Fintype.sum_eq_single (i, o) (fun x hx => by simp [hx])]
    rw [Fintype.sum_eq_single (j, o) (fun x hx => by simp [hx])]
    simp
  rw [this]
  exact Matrix.posSemidef_sum _ (fun o _ => hS.mul_mul_conjTranspose_same _)

theorem g59d_NS_of {A B C D : Type} [Fintype A] [Fintype C] (S : Op ((A × B) × (C × D)))
    (h : ChoiNS S) : g59d_NS' S := by
  refine ⟨fun bd bd' => (Fintype.card A : ℂ)⁻¹ * ∑ x : A, ∑ c : C, S ((x,bd.1),(c,bd.2)) ((x,bd'.1),(c,bd'.2)), ?_⟩
  intro a aa b bb d dd
  rw [h a aa b bb d dd]
  split_ifs <;> simp

theorem g59d_of_NS {A B C D : Type} [Fintype A] [Nonempty A] [Fintype C] (S : Op ((A × B) × (C × D)))
    (h : g59d_NS' S) : ChoiNS S := by
  obtain ⟨W, hW⟩ := h
  intro a aa b bb d dd
  have hx : ∀ x : A, ∑ c : C, S ((x,b),(c,d)) ((x,bb),(c,dd)) = W (b,d) (bb,dd) := by
    intro x; rw [hW]; simp
  simp only [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hW]
  have : (Fintype.card A : ℂ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this.ne'
  split_ifs
  · field_simp
  · simp

def g59d_Gam {A B C D E F K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {ι1 ι2 ι3 ι4 : Type} [Fintype ι1] [Fintype ι2] [Fintype ι3] [Fintype ι4]
    (P : ι1 → Matrix A E ℂ) (Q : ι2 → Matrix B F ℂ) (R : ι3 → Matrix K C ℂ) (T : ι4 → Matrix L D ℂ)
    (J : Op ((A × B) × (C × D))) : Op ((E × F) × (K × L)) :=
  ∑ st : (ι1 × ι2) × (ι3 × ι4),
      Matrix.kronecker (Matrix.kronecker (P st.1.1) (Q st.1.2)).transpose
        (Matrix.kronecker (R st.2.1) (T st.2.2)) * J *
      (Matrix.kronecker (Matrix.kronecker (P st.1.1) (Q st.1.2)).transpose
        (Matrix.kronecker (R st.2.1) (T st.2.2)))ᴴ

section
variable {A B C D E F K L : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] [Fintype K] [Fintype L]
    {ι1 ι2 ι3 ι4 : Type} [Fintype ι1] [Fintype ι2] [Fintype ι3] [Fintype ι4]
    (P : ι1 → Matrix A E ℂ) (Q : ι2 → Matrix B F ℂ) (R : ι3 → Matrix K C ℂ) (T : ι4 → Matrix L D ℂ)

omit [Fintype E] [Fintype F] [Fintype K] [Fintype L] in
theorem g59d_Gam_add (X Y : Op ((A × B) × (C × D))) :
    g59d_Gam P Q R T (X + Y) = g59d_Gam P Q R T X + g59d_Gam P Q R T Y := by
  simp only [g59d_Gam, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

omit [Fintype E] [Fintype F] [Fintype K] [Fintype L] in
theorem g59d_Gam_sub (X Y : Op ((A × B) × (C × D))) :
    g59d_Gam P Q R T (X - Y) = g59d_Gam P Q R T X - g59d_Gam P Q R T Y := by
  simp only [g59d_Gam, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem g59d_Gam_psd (X : Op ((A × B) × (C × D))) (hX : X.PosSemidef) :
    (g59d_Gam P Q R T X).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => hX.mul_mul_conjTranspose_same _)

omit [Fintype E] [Fintype F] [Fintype K] [Fintype L] in
theorem g59d_Gam_herm (X : Op ((A × B) × (C × D))) (hX : X.IsHermitian) :
    (g59d_Gam P Q R T X).IsHermitian :=
  g59d_herm_sum _ (fun _ => Matrix.isHermitian_mul_mul_conjTranspose _ hX)

omit [Fintype E] [Fintype F] [Fintype K] [Fintype L] in
theorem g59d_Gam_T (X : Op ((A × B) × (C × D))) :
    transposeBobChoi (g59d_Gam P Q R T X) =
      g59d_Gam P (fun j => (Q j).map star) R (fun l => (T l).map star) (transposeBobChoi X) := by
  rw [g59d_Gam, g59d_tB_sum]
  simp only [g59d_T_conj]
  rfl

theorem g59d_Gam_trO [DecidableEq C] [DecidableEq D] (hR : ∑ k, (R k)ᴴ * R k = 1)
    (hT : ∑ l, (T l)ᴴ * T l = 1) (X : Op ((A × B) × (C × D))) :
    traceOutput (g59d_Gam P Q R T X) =
      ∑ s : ι1 × ι2, (Matrix.kronecker (P s.1) (Q s.2)).transpose * traceOutput X *
        ((Matrix.kronecker (P s.1) (Q s.2)).transpose)ᴴ :=
  g59d_traceOutput_sandwich (fun s : ι1 × ι2 => Matrix.kronecker (P s.1) (Q s.2))
    (fun t : ι3 × ι4 => Matrix.kronecker (R t.1) (T t.2)) (g59d_kron_tp R T hR hT) X

end

theorem g59d_beta_le {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] {C : Type} [Fintype C] {D : Type} [Fintype D]
    {E : Type} [Fintype E] [Nonempty E] {F : Type} [Fintype F]
    {K : Type} [Fintype K] {L : Type} [Fintype L]
    (M : Superop (A × B) (C × D)) (hM : CP M)
    (preA : Superop E A) (preB : Superop F B)
    (postA : Superop C K) (postB : Superop D L)
    (hpreA : IsChannel preA) (hpreB : IsChannel preB)
    (hpostA : IsChannel postA) (hpostB : IsChannel postB) :
    bipartiteBeta (tensorAction postA postB ∘ M ∘ tensorAction preA preB) ≤ bipartiteBeta M := by
  obtain ⟨mm, Mk, hMk⟩ := hM
  obtain ⟨m1, P, hP, hPe⟩ := hpreA
  obtain ⟨m2, Q, hQ, hQe⟩ := hpreB
  obtain ⟨m3, R, hR, hRe⟩ := hpostA
  obtain ⟨m4, T, hT, hTe⟩ := hpostB
  have eM : M = krausApply Mk := funext hMk
  have eP : preA = krausApply P := funext hPe
  have eQ : preB = krausApply Q := funext hQe
  have eR : postA = krausApply R := funext hRe
  have eT : postB = krausApply T := funext hTe
  subst eM eP eQ eR eT
  have eN : (tensorAction (krausApply R) (krausApply T) ∘ krausApply Mk ∘
      tensorAction (krausApply P) (krausApply Q)) =
      fun ρ => krausApply (fun t : Fin m3 × Fin m4 => Matrix.kronecker (R t.1) (T t.2))
        (krausApply Mk (krausApply (fun s : Fin m1 × Fin m2 => Matrix.kronecker (P s.1) (Q s.2)) ρ)) := by
    funext ρ
    simp only [Function.comp, g59d_tensor_kraus]
  have hchoi : choi (tensorAction (krausApply R) (krausApply T) ∘ krausApply Mk ∘
      tensorAction (krausApply P) (krausApply Q)) = g59d_Gam P Q R T (choi (krausApply Mk)) := by
    rw [eN, g59d_choi_sandwich]
    rfl
  unfold bipartiteBeta
  apply le_sInf
  rintro r ⟨S, V, ⟨hSh, hVh, hT1, hT2, hSV1, hSV2, hNS⟩, rfl⟩
  have hSpsd : S.PosSemidef := by
    have h2 := hSV1.add hSV2
    have e : S + V + (S - V) = (2 : ℂ) • S := by rw [two_smul]; abel
    rw [e] at h2
    have := h2.smul (show (0 : ℂ) ≤ (1/2 : ℂ) by rw [Complex.nonneg_iff]; norm_num)
    rwa [smul_smul, show (1/2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
  apply sInf_le_of_le (b := ((specNorm (traceOutput (g59d_Gam P Q R T S)) : ℝ) : EReal))
  · refine ⟨g59d_Gam P Q R T S, g59d_Gam P Q R T V, ⟨g59d_Gam_herm P Q R T S hSh,
      g59d_Gam_herm P Q R T V hVh, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · rw [hchoi, ← g59d_Gam_add, g59d_Gam_T]; exact g59d_Gam_psd _ _ _ _ _ hT1
    · rw [hchoi, ← g59d_Gam_sub, g59d_Gam_T]; exact g59d_Gam_psd _ _ _ _ _ hT2
    · rw [← g59d_Gam_add]; exact g59d_Gam_psd _ _ _ _ _ hSV1
    · rw [← g59d_Gam_sub]; exact g59d_Gam_psd _ _ _ _ _ hSV2
    · exact g59d_of_NS _ (g59d_NS_pres P Q R T hP hR S (g59d_NS_of S hNS))
  · rw [g59d_Gam_trO P Q R T hR hT]
    have := g59d_spec_le (fun s : Fin m1 × Fin m2 => (Matrix.kronecker (P s.1) (Q s.2)).transpose)
      (g59d_transpose_unital _ (g59d_kron_tp P Q hP hQ)) (traceOutput S) (g59d_traceOutput_psd S hSpsd)
    exact_mod_cast this

end QAlgorithms.Papers.Independent.Dependency50.P09

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P09
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Corollary 7 (Data processing under local channels), arXiv:2010.01058v3, PDF pp.8.
 -/
theorem solution {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    {K : Type} [Fintype K] [Nonempty K]
    {L : Type} [Fintype L] [Nonempty L]
    (M : Superop (A × B) (C × D)) (hM : CP M)
    (preA : Superop E A) (preB : Superop F B)
    (postA : Superop C K) (postB : Superop D L)
    (hpreA : IsChannel preA) (hpreB : IsChannel preB)
    (hpostA : IsChannel postA) (hpostB : IsChannel postB) :
    cBeta (tensorAction postA postB ∘ M ∘ tensorAction preA preB) ≤ cBeta M := by
  exact g59d_logExt_mono (g59d_beta_le M hM preA preB postA postB hpreA hpreB hpostA hpostB)

end
