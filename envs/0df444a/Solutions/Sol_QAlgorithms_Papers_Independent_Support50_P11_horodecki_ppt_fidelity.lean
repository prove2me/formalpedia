-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P11.horodecki_ppt_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:53:11.72243+00:00
-- url     : https://prove2.me/submissions/1b12ebca-123c-415d-8ee7-5951700884ec

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Mathlib

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)
open QAlgorithms.Papers.Independent.Information100.P21 (pt)

section S190P11
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S190P11_ch_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ]
  unfold krausApply
  calc (∑ j, E j * X * (E j)ᴴ).trace = ∑ j, ((E j)ᴴ * E j * X).trace := by
        rw [Matrix.trace_sum]; congr 1; ext j; rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (E j)ᴴ * E j) * X).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, Matrix.one_mul]

lemma S190P11_ch_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) (c : ℂ) (X : Matrix ι ι ℂ) : Φ (c • X) = c • Φ X := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ, hΦ]
  unfold krausApply
  simp [Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma S190P11_choi_psd {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι} {Φ : Superop ι κ}
    (h : IsChannel Φ) : (choi Φ).PosSemidef := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  have : choi Φ = ∑ j, Matrix.vecMulVec (fun p : ι × κ => E j p.2 p.1)
      (star (fun p : ι × κ => E j p.2 p.1)) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    simp [choi, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMulVec_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _

lemma S190P11_pt_single {A B : Type*} [DecidableEq A] [DecidableEq B] (a b : A) (β γ : B) :
    pt (Matrix.single (a, β) (b, γ) (1 : ℂ)) = Matrix.single (a, γ) (b, β) 1 := by
  ext p q
  simp only [pt, Matrix.single_apply, Prod.ext_iff]
  by_cases h1 : a = p.1 <;> by_cases h2 : γ = p.2 <;> by_cases h3 : b = q.1 <;>
    by_cases h4 : β = q.2 <;> simp [h1, h2, h3, h4]

lemma S190P11_contract {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y)).PosSemidef := by
  have hH := (hP.submatrix (Prod.snd : U × X → X)).hadamard hQ
  let A : Matrix (U × X) U ℂ := Matrix.of fun p u => if p.1 = u then 1 else 0
  have := hH.conjTranspose_mul_mul_same A
  have key : (Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y)) =
      Aᴴ * (P.submatrix Prod.snd Prod.snd ⊙ Q) * A := by
    ext u v
    simp [A, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.hadamard_apply]
    exact Finset.sum_comm
  rw [key]; exact this

lemma S190P11_contract' {U X : Type*} [Fintype U] [Fintype X] {P : Matrix X X ℂ}
    {Q : Matrix (U × X) (U × X) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (M : Matrix U U ℂ) (hM : ∀ u v, M u v = ∑ x, ∑ y, P x y * Q (u, x) (v, y)) :
    M.PosSemidef := by
  rw [show M = Matrix.of fun u v => ∑ x, ∑ y, P x y * Q (u, x) (v, y) from Matrix.ext hM]
  exact S190P11_contract hP hQ

lemma S190P11_offdiag {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) (x y : n) :
    (M x y).re + (M y x).re ≤ (M x x).re + (M y y).re := by
  have h2 := (hM.submatrix ![x, y]).re_dotProduct_nonneg ![1, -1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h2
  linarith

lemma S190P11_fid (K : ℕ) (hK : 0 < K) (L : Superop (Fin K) (Fin K))
    (hL : ∀ (c : ℂ) X, L (c • X) = c • L X) :
    channelFidelity K L = ((K:ℝ)^2)⁻¹ * (∑ a, ∑ b, L (Matrix.single a b 1) a b).re := by
  unfold channelFidelity
  rw [dif_pos hK]
  unfold QuditFidelity.entanglementFidelity effectProb
  simp only [pureDensity, finiteMaxEntangled, idTensorSuperop, Matrix.trace, Matrix.mul_apply,
    Matrix.diag, Fintype.card_fin, Matrix.of_apply]
  have hs : (starRingEnd ℂ) ((↑(√(K:ℝ)) : ℂ)⁻¹) = (↑(√(K:ℝ)) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  have hss : ((↑(√(K:ℝ)) : ℂ)⁻¹) * (↑(√(K:ℝ)) : ℂ)⁻¹ = (K:ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hM : ∀ a b : Fin K, (Matrix.of fun i_1 i' =>
      (if a = i_1 then (↑(√(K:ℝ)) : ℂ)⁻¹ else 0) *
        (starRingEnd ℂ) (if b = i' then (↑(√(K:ℝ)) : ℂ)⁻¹ else 0)) =
      (K:ℂ)⁻¹ • Matrix.single a b 1 := by
    intro a b; ext x y
    simp only [apply_ite (starRingEnd ℂ), hs, map_zero, Matrix.of_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp_rw [hM, hL]
  simp only [apply_ite (starRingEnd ℂ), hs, map_zero, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.smul_apply, smul_eq_mul, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
    (fun b _ hb => by simp [Ne.symm hb]))]
  simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  simp_rw [← mul_assoc, hss, ← Finset.mul_sum]
  rw [Finset.sum_comm, show ((K:ℂ)⁻¹ * (K:ℂ)⁻¹ * ∑ y, ∑ x, L (Matrix.single y x 1) y x) =
    ((((K:ℝ)^2)⁻¹ : ℝ) : ℂ) * ∑ y, ∑ x, L (Matrix.single y x 1) y x by push_cast; ring,
    Complex.re_ofReal_mul]

lemma S190P11_link_smul {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (c : ℂ) (X : Matrix (Fin K) (Fin K) ℂ) :
    link K N Z (c • X) = c • link K N Z X := by
  ext b d
  simp [link, Finset.mul_sum, mul_assoc]

lemma S190P11_link_entry {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (N : Superop I O)
    (Z : Superop (Fin K × O) (I × Fin K)) (a b : Fin K) :
    link K N Z (Matrix.single a b 1) a b = ∑ i, ∑ j, ∑ β, ∑ γ,
      N (Matrix.single i j 1) β γ * Z (Matrix.single (a, β) (b, γ) 1) (i, a) (j, b) := by
  simp [link, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

lemma S190P11_upper {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (N : Superop I O) (hN : Horodecki N) (Z : Superop (Fin K × O) (I × Fin K))
    (hZ : IsForwardCode K .PPTp Z) : channelFidelity K (link K N Z) ≤ 1 / K := by
  obtain ⟨hZc, ⟨E, hE, hEZ⟩, hppt⟩ := hZ
  have hppt' : PPTMap Z := hppt
  have hC' := S190P11_choi_psd hppt'.2
  let f : (Fin K × Fin K) × (I × O) → (Fin K × O) × (I × Fin K) :=
    fun w => ((w.1.1, w.2.2), (w.2.1, w.1.2))
  let M : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ := fun u v =>
    ∑ x : I × O, ∑ y : I × O, N (Matrix.single x.1 y.1 1) y.2 x.2 *
      Z (Matrix.single (u.1, y.2) (v.1, x.2) 1) (x.1, v.2) (y.1, u.2)
  have hMe : ∀ u v, M u v = ∑ x : I × O, ∑ y : I × O, N (Matrix.single x.1 y.1 1) y.2 x.2 *
      Z (Matrix.single (u.1, y.2) (v.1, x.2) 1) (x.1, v.2) (y.1, u.2) := fun _ _ => rfl
  have hMpsd : M.PosSemidef := S190P11_contract' hN.2 (hC'.submatrix f) M (by
    intro u v
    simp only [M, pt, choi, Matrix.submatrix_apply, f, S190P11_pt_single]
    congr!)
  rw [S190P11_fid K hK _ (S190P11_link_smul K N Z)]
  have h1 : ∑ a, ∑ b, link K N Z (Matrix.single a b 1) a b = ∑ a, ∑ b, M (a, b) (b, a) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [S190P11_link_entry, hMe]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_comm
  have h2 : (∑ a, ∑ b, M (a, b) (b, a)).re ≤ (∑ a, ∑ b, M (a, b) (a, b)).re := by
    have hoff := fun a b => S190P11_offdiag hMpsd (a, b) (b, a)
    simp only [Complex.re_sum]
    have hsw1 : ∑ a, ∑ b, (M (b, a) (a, b)).re = ∑ a, ∑ b, (M (a, b) (b, a)).re :=
      Finset.sum_comm
    have hsw2 : ∑ a, ∑ b, (M (b, a) (b, a)).re = ∑ a, ∑ b, (M (a, b) (a, b)).re :=
      Finset.sum_comm
    have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hoff a b
    simp only [Finset.sum_add_distrib] at this
    linarith
  have htrs : ∀ (a : Fin K) (β γ : O), traceRight (Matrix.single (a, β) (a, γ) (1 : ℂ)) =
      (if β = γ then (1 : ℂ) else 0) • Matrix.single a a 1 := by
    intro a β γ; ext x y
    simp only [traceRight, Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases hxy : a = x ∧ a = y
    · obtain ⟨rfl, rfl⟩ := hxy
      rcases eq_or_ne β γ with rfl | h3
      · simp
      · rw [if_neg h3, zero_mul]
        exact Finset.sum_eq_zero fun k _ => if_neg (fun h => h3 (h.1.2.trans h.2.2.symm))
    · rw [if_neg hxy, mul_zero]
      exact Finset.sum_eq_zero fun k _ => if_neg (fun h => hxy ⟨h.1.1, h.2.1⟩)
  have hTr : ∀ a, ∑ c, M (a, c) (a, c) = 1 := by
    intro a
    simp only [hMe]
    calc _ = ∑ x : I × O, ∑ y : I × O, N (Matrix.single x.1 y.1 1) y.2 x.2 *
          traceRight (Z (Matrix.single (a, y.2) (a, x.2) 1)) x.1 y.1 := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => ?_
          simp [traceRight, Finset.mul_sum]
      _ = ∑ x : I × O, ∑ y : I × O, N (Matrix.single x.1 y.1 1) y.2 x.2 *
          ((if y.2 = x.2 then (1 : ℂ) else 0) * E (Matrix.single a a 1) x.1 y.1) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [hEZ, htrs, S190P11_ch_smul hE]; rfl
      _ = ∑ i, ∑ j, (N (Matrix.single i j 1)).trace * E (Matrix.single a a 1) i j := by
          simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          simp [mul_ite, ite_mul, Finset.sum_ite_eq']
      _ = ∑ i, E (Matrix.single a a 1) i i := by
          simp only [S190P11_ch_trace hN.1]
          simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]
      _ = 1 := by
          rw [show ∑ i, E (Matrix.single a a 1) i i = (E (Matrix.single a a 1)).trace from rfl,
            S190P11_ch_trace hE]
          simp
  have h3 : ∑ a, ∑ b, M (a, b) (a, b) = K := by
    simp [hTr]
  rw [h1]
  refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans ?_
  rw [h3, Complex.natCast_re, pow_two, mul_inv, mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hK.ne'), mul_one, one_div]

lemma S190P11_isChannel_of {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    {_ : DecidableEq ι} {Φ : Superop ι κ} (A : ι' → Matrix κ ι ℂ)
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card ι', fun j => A ((Fintype.equivFin ι').symm j), ?_, fun ρ => ?_⟩
  · show ∑ j, _ = 1
    rw [Equiv.sum_comp ((Fintype.equivFin ι').symm) (fun k => (A k)ᴴ * A k)]
    exact hA
  · rw [hΦ]
    show _ = ∑ j, _
    exact (Equiv.sum_comp _ (fun k => A k * ρ * (A k)ᴴ)).symm

lemma S190P11_lower {I O : Type} [Fintype I] [Nonempty I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (N : Superop I O) (hN : IsChannel N) :
    ∃ Z, IsForwardCode K .PPTp Z ∧ channelFidelity K (link K N Z) = 1 / K := by
  let i0 : I := Classical.arbitrary I
  let Z0 : Superop (Fin K × O) (I × Fin K) := fun X p q =>
    if p.1 = i0 ∧ q.1 = i0 ∧ p.2 = q.2 then ∑ β, X (p.2, β) (p.2, β) else 0
  have hZ0 : ∀ {_ : DecidableEq (Fin K × O)}, IsChannel Z0 := by
    intro _
    refine S190P11_isChannel_of (fun (k : Fin K × O) => Matrix.of fun (p : I × Fin K) (r : Fin K × O) =>
      if p = (i0, k.1) ∧ r = k then (1 : ℂ) else 0) ?_ ?_
    · ext r s
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply]
      rw [Finset.sum_eq_single s (fun c _ hc => Finset.sum_eq_zero fun j _ => by
        simp [Ne.symm hc]) (by simp)]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
    · intro X; ext ⟨p1, p2⟩ ⟨q1, q2⟩
      simp only [Z0, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fintype.sum_prod_type, Prod.mk.injEq]
      by_cases h1 : p1 = i0 <;> by_cases h2 : q1 = i0 <;> by_cases h3 : p2 = q2 <;>
        simp [h1, h2, h3, @eq_comm _ q2 p2, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq,
          apply_ite (starRingEnd ℂ), mul_ite]
  have hpt : (fun X => pt (Z0 (pt X))) = Z0 := by
    funext X; ext p q
    by_cases h : p.2 = q.2
    · simp [Z0, pt, h, eq_comm]
    · simp [Z0, pt, h, Ne.symm h]
  let E0 : Superop (Fin K) I := fun Y i j => if i = i0 ∧ j = i0 then Y.trace else 0
  have hE0 : ∀ {_ : DecidableEq (Fin K)}, IsChannel E0 := by
    intro _
    refine S190P11_isChannel_of (fun (k : Fin K) => Matrix.of fun (i : I) (a : Fin K) =>
      if i = i0 ∧ a = k then (1 : ℂ) else 0) ?_ ?_
    · ext r s
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply]
      rw [Finset.sum_eq_single s (fun c _ hc => Finset.sum_eq_zero fun j _ => by
        simp [Ne.symm hc]) (by simp)]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
    · intro X; ext p q
      simp only [E0, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Matrix.trace, Matrix.diag]
      by_cases h1 : p = i0 <;> by_cases h2 : q = i0 <;>
        simp [h1, h2, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]
  refine ⟨Z0, ⟨hZ0, ⟨E0, hE0, fun X => ?_⟩, ⟨hZ0, ?_⟩⟩, ?_⟩
  · ext i j
    simp [traceRight, Z0, E0, Matrix.trace]
  · rw [hpt]; exact hZ0
  · have hent : ∀ a b, link K N Z0 (Matrix.single a b 1) a b = if a = b then 1 else 0 := by
      intro a b
      rw [S190P11_link_entry]
      by_cases hab : a = b
      · subst hab
        have hs : ∀ β γ : O, ∑ β', Matrix.single (a, β) (a, γ) (1 : ℂ) (a, β') (a, β') =
            if β = γ then 1 else 0 := by
          intro β γ
          rw [Finset.sum_eq_single β]
          · simp only [Matrix.single_apply, Prod.mk.injEq]
            by_cases h : β = γ
            · simp [h]
            · simp [h, Ne.symm h]
          · intro b _ hb; exact Matrix.single_apply_of_row_ne (by simp [Ne.symm hb]) _ _ _
          · simp
        simp only [Z0, hs, and_true, mul_ite, mul_zero, mul_one]
        simp [Finset.sum_ite_eq', ite_and]
        have := S190P11_ch_trace hN (Matrix.single i0 i0 1)
        simpa [Matrix.trace] using this
      · simp [Z0, hab]
    rw [S190P11_fid K hK _ (S190P11_link_smul K N Z0)]
    simp only [hent, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    simp
    field_simp

end S190P11

end QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P11 in
theorem solution {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (N : Superop I O) (hN : Horodecki N) (K : ℕ) (hK : 0 < K) :
    optimalCodeFidelity .PPTp N K = 1 / (K : ℝ) := by
  obtain ⟨Z0, hZ0, hf⟩ := S190P11_lower K hK N hN.1
  unfold optimalCodeFidelity
  refine IsGreatest.csSup_eq ⟨⟨Z0, hZ0, hf.symm⟩, ?_⟩
  rintro f ⟨Z, hZ, rfl⟩
  exact S190P11_upper K hK N hN Z hZ

