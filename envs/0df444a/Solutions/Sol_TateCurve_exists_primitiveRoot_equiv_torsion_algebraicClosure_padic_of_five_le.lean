-- Prove2me | solution 1 for TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9853edb4-a24f-5bbe-b65b-9b960d4c7094

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_TateCurve_tateTorsionEquiv_add
import Theorems.Thm_Padic_exists_complete_algClosed_isometry_algebraicClosure
import Theorems.Thm_TateCurve_tateTorsionPoint_map
import Theorems.Thm_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine TateCurve

set_option maxHeartbeats 8000000

namespace C2cSketch

variable {K : Type} [Field K] [DecidableEq K]

private noncomputable def torsionByAddEquivOfEq {W W' : WeierstrassCurve K} (h : W = W') (p : ℕ) :
    W.n_torsionGen p ≃+ W'.n_torsionGen p := by
  subst h; exact AddEquiv.refl _

private lemma torsionByAddEquivOfEq_symm_apply_val {W W' : WeierstrassCurve K} (h : W = W')
    (p : ℕ) (P : W'.n_torsionGen p) :
    (((torsionByAddEquivOfEq h p).symm P : W.n_torsionGen p) : W.toAffine.Point)
      = h.symm ▸ (P : W'.toAffine.Point) := by
  subst h; rfl

private lemma transport_point_some {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    (h.symm ▸ (Affine.Point.some x y hns : W'.toAffine.Point) : W.toAffine.Point)
      = Affine.Point.some x y (h.symm ▸ hns) := by
  subst h; rfl

private lemma transport_point_zero {W W' : WeierstrassCurve K} (h : W = W') :
    (h.symm ▸ (0 : W'.toAffine.Point) : W.toAffine.Point) = 0 := by
  subst h; rfl

private lemma transport_nonsingular {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular x y := by
  subst h; exact hns

private lemma ps_congr {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

end C2cSketch

open C2cSketch

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨K, instNF, instUM, instCS, instCZ, instAC, instAlg, hiso, ι, hext⟩ :=
    Padic.exists_complete_algClosed_isometry_algebraicClosure p
  letI := instNF; letI := instUM; letI := instCS; letI := instCZ; letI := instAC; letI := instAlg
  letI : DecidableEq K := Classical.decEq _

  set qBar := algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT with hqBar_def
  have hqBar0 : qBar ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[p] _).injective (h.trans (map_zero _).symm)
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ_[p]) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ_[p]))
    (Polynomial.degree_cyclotomic_pos p _ hp.pos).ne'
  have hζ : IsPrimitiveRoot ζ p := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq qBar (n := p) hp.pos
  refine ⟨ζ, t, hζ, ht, ?_⟩

  set q_K := algebraMap ℚ_[p] K qT with hq_K_def
  have hq_K0 : q_K ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[p] K).injective (h.trans (map_zero _).symm)
  have hq_K1 : ‖q_K‖₊ < 1 := by
    have h : ‖q_K‖ < 1 := by rw [hq_K_def, hiso]; exact_mod_cast hqT1
    exact_mod_cast h
  have hιinj : Function.Injective ι := RingHom.injective ι.toRingHom
  set ζ_K := ι ζ with hζ_K_def
  set t_K := ι t with ht_K_def
  have hζ_K : IsPrimitiveRoot ζ_K p := hζ.map_of_injective hιinj
  have ht_K : t_K ^ p = q_K := by
    rw [ht_K_def, ← map_pow, ht, hqBar_def, hq_K_def]; exact ι.commutes qT
  have hζ_K0 : ζ_K ≠ 0 := hζ_K.ne_zero (by omega)
  have ht_K0 : t_K ≠ 0 := fun h0 => hq_K0 (by rw [← ht_K, h0, zero_pow hp.ne_zero])

  obtain ⟨hcurve_eq, hbij⟩ :=
    TateCurve.torsionBy_baseChange_bijective_algebraicClosure_padic p hp5 qT hqT0 hqT1 K hiso ι

  have hcurve_eq' : ((TateCurve.curve qT)⁄K : WeierstrassCurve K) = TateCurve.curve q_K := hcurve_eq

  let br₁Fwd : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p →+
               Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p :=
    { toFun := fun P =>
        ⟨Point.map ι (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩
      map_zero' := Subtype.ext (AddMonoidHom.map_zero _)
      map_add' := fun P Q => Subtype.ext (AddMonoidHom.map_add _ _ _) }
  let br₁ : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p ≃+
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p :=
    AddEquiv.ofBijective br₁Fwd hbij
  have hbr₁_val : ∀ X,
      (↑(br₁ X) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι (↑X : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point) :=
    fun _ => rfl

  let br₂ : ((TateCurve.curve qT)⁄K).n_torsionGen p ≃+ (TateCurve.curve q_K).n_torsionGen p :=
    torsionByAddEquivOfEq hcurve_eq' p

  let tte_K := TateCurve.tateTorsionEquiv q_K ζ_K t_K hq_K0 hq_K1 Fact.out hp5 hζ_K ht_K
  let tte_K_add : (Fin p × Fin p) ≃+ (TateCurve.curve q_K).n_torsionGen p :=
    { tte_K with
      map_add' := fun a b => Subtype.ext <|
        TateCurve.tateTorsionEquiv_add hq_K0 hq_K1 hp5 hζ_K ht_K a b }

  let zm : (ZMod p × ZMod p) ≃+ (Fin p × Fin p) :=
    { toFun := fun a => (⟨a.1.val, a.1.val_lt⟩, ⟨a.2.val, a.2.val_lt⟩)
      invFun := fun i => ((i.1 : ZMod p), (i.2 : ZMod p))
      left_inv := fun a => by ext <;> simp [ZMod.natCast_val, ZMod.cast_id']
      right_inv := fun i => by
        ext <;> simp only [ZMod.val_natCast_of_lt (Fin.isLt _)] <;> rfl
      map_add' := fun a b => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Fin.add_def, Fin.mk.injEq, ZMod.val_add] }

  let φAdd : (ZMod p × ZMod p) ≃+
      Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p :=
    zm.trans (tte_K_add.trans (br₂.symm.trans br₁.symm))

  have hφ_char : ∀ (a b : ZMod p),
      (Point.map ι ↑(φAdd (a, b)) : ((TateCurve.curve qT)⁄K).Point)
        = hcurve_eq'.symm ▸
          (tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val
            : (TateCurve.curve q_K).toAffine.Point) := by
    intro a b
    have htte : (↑(tte_K_add (zm (a, b))) : (TateCurve.curve q_K).toAffine.Point)
        = tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val := by
      have step1 : ∀ x, (↑(tte_K_add x) : (TateCurve.curve q_K).toAffine.Point)
          = (↑(tte_K x) : (TateCurve.curve q_K).toAffine.Point) := fun _ => rfl
      rw [step1]
      simp only [tte_K, tateTorsionEquiv, Equiv.ofBijective_apply]
      rfl
    have h0 : br₁ (φAdd (a, b)) = br₂.symm (tte_K_add (zm (a, b))) := br₁.apply_symm_apply _
    have h1 : (↑(br₁ (φAdd (a, b))) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι ↑(φAdd (a, b)) := hbr₁_val (φAdd (a, b))
    have h2 : (↑(br₂.symm (tte_K_add (zm (a, b)))) : ((TateCurve.curve qT)⁄K).toAffine.Point)
        = hcurve_eq'.symm ▸ (↑(tte_K_add (zm (a, b))) : (TateCurve.curve q_K).toAffine.Point) :=
      torsionByAddEquivOfEq_symm_apply_val hcurve_eq' p _
    rw [← h1, h0, h2, htte]
  refine ⟨φAdd.toEquiv, ?_, ?_⟩
  ·
    intro a b
    rw [show φAdd.toEquiv (a + b) = φAdd (a + b) from rfl, φAdd.map_add]
    exact Submodule.coe_add _ _
  ·
    intro σ e c hσζ hσt i j
    obtain ⟨σK, hσKiso, hext_σ⟩ := hext σ
    have hσKinj : Function.Injective σK := hσKiso.injective
    have hσKq : σK q_K = q_K := by
      rw [hq_K_def, ← ι.commutes qT, hext_σ,
        show σ (algebraMap ℚ_[p] _ qT) = algebraMap ℚ_[p] _ qT from σ.commutes qT]
    have hσKζ : σK ζ_K = ζ_K ^ e := by rw [hζ_K_def, hext_σ, hσζ, map_pow]
    have hσKt : σK t_K = ζ_K ^ c * t_K := by
      rw [ht_K_def, hext_σ, hσt, map_mul, map_pow]

    let σK_alg : K →ₐ[ℚ_[p]] K :=
      { toRingHom := σK
        commutes' := fun r => by
          show σK (algebraMap ℚ_[p] K r) = algebraMap ℚ_[p] K r
          rw [← ι.commutes r, hext_σ, σ.commutes r] }
    have hcomp : (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K).comp σ.toAlgHom = σK_alg.comp ι :=
      AlgHom.ext fun x => (hext_σ x).symm
    have hfunc : ∀ (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
        Point.map ι (Point.map σ.toAlgHom P) = Point.map σK_alg (Point.map ι P) := by
      intro P
      calc Point.map ι (Point.map σ.toAlgHom P)
          = Point.map ((ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K).comp σ.toAlgHom) P := by
            cases P <;> rfl
        _ = Point.map (σK_alg.comp ι) P := by rw [hcomp]
        _ = Point.map σK_alg (Point.map ι P) := by cases P <;> rfl

    apply hbij.1
    apply Subtype.ext
    show Point.map ι ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
        = Point.map ι ((φAdd (e • i + c • j, j) :
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
          : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
    have hsmul_val : ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
        = Point.map σ.toAlgHom
            (φAdd (i, j) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point) := rfl
    rw [hsmul_val, hfunc, hφ_char i j, hφ_char (e • i + c • j) j]
    have hnsmul_val : ∀ (n : ℕ) (x : ZMod p), (n • x).val = (n * x.val) % p := by
      intro n x
      induction n with
      | zero => simp [Nat.zero_mod]
      | succ m ih =>
        rw [succ_nsmul, ZMod.val_add, ih, Nat.succ_mul, Nat.mod_add_mod]
    have hval : (e • i + c • j).val = (e * i.val + c * j.val) % p := by
      rw [ZMod.val_add, hnsmul_val e i, hnsmul_val c j, Nat.add_mod_mod, Nat.mod_add_mod]
    rw [hval]
    by_cases hij0 : i.val = 0 ∧ j.val = 0
    · obtain ⟨hi0, hj0⟩ := hij0
      simp only [hi0, hj0, mul_zero, add_zero, Nat.zero_mod, tateTorsionPoint_zero_zero,
        transport_point_zero hcurve_eq', AddMonoidHom.map_zero]
    · have hi_lt : i.val < p := i.val_lt
      have hj_lt : j.val < p := j.val_lt
      set i₂ := (e * i.val + c * j.val) % p with hi₂def
      have hi₂ : i₂ < p := Nat.mod_lt _ hp.pos
      have hpe : ¬ p ∣ e := by
        intro hdvd
        obtain ⟨k, rfl⟩ := hdvd
        have h1 : ζ_K ^ (p * k) = 1 := by rw [pow_mul, hζ_K.pow_eq_one, one_pow]
        exact hζ_K.ne_one (by omega) (hσKinj ((hσKζ.trans h1).trans (map_one σK).symm))
      have hij₂ : ¬(i₂ = 0 ∧ j.val = 0) := by
        rintro ⟨h1, h2⟩
        refine hij0 ⟨?_, h2⟩
        rw [hi₂def, h2, mul_zero, add_zero] at h1
        rcases Nat.eq_zero_or_pos i.val with h0 | hpos
        · exact h0
        · exact absurd
            (Nat.le_of_dvd hpos
              ((Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h1) |>.resolve_left hpe))
            (by omega)
      rw [tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi_lt hj_lt hij0,
          transport_point_some hcurve_eq' _,
          tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi₂ hj_lt hij₂,
          transport_point_some hcurve_eq' _]

      have hX : σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointX q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointX_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hY : σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointY q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointY_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hns_target : ((TateCurve.curve qT)⁄K).toAffine.Nonsingular
          (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
          (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) := by
        rw [hX, hY]
        exact transport_nonsingular hcurve_eq'
          (nonsingular_point hq_K0 hq_K1 (tateParam_ne_zero hζ_K0 ht_K0)
            (tateParam_offLattice hq_K0 hq_K1 hζ_K ht_K hi₂ hj_lt hij₂))
      calc (Point.map σK_alg (Affine.Point.some (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i.val * t_K ^ j.val)) _)
            : ((TateCurve.curve qT)⁄K).Point)
          = Affine.Point.some (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
              (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) hns_target := rfl
        _ = Affine.Point.some (pointX q_K (ζ_K ^ i₂ * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i₂ * t_K ^ j.val)) _ := ps_congr hX hY hns_target _

end S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
end P2MW
export P2MW.S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le (solution)
