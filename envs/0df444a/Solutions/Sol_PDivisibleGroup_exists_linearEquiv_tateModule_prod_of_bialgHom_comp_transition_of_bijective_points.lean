-- Prove2me | solution 1 for PDivisibleGroup.exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a67e0449-31b9-5b01-ada1-691143886d00

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points

set_option autoImplicit false

namespace PT

open PDivisibleGroup

theorem exists_point_of_smul_eq_zero {R : Type} [CommRing R] {p k : ℕ} [Fact p.Prime] (X : PDivisibleGroup R p k)
    (L : Type) [CommRing L] [Algebra R L] (z : X.Points L) (n : ℕ) (hz : ((p ^ n : ℕ) : ℤ) • z = 0) :
    ∃ g : X.Point L n, X.pointsMkAdd L n (Additive.ofMul g) = z := by
  obtain ⟨v, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd X z

  have hxw := X.pointsMkAdd_pointInclLE (L := L) (le_max_left v n) x
  rw [← hxw] at hz ⊢
  have hpow : X.pointInclLE L (le_max_left v n) x ^ (p ^ n) = 1 :=
    Additive.ofMul.injective (X.pointsMkAdd_injective (L := L) (max v n)
      (by rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul, hz]))
  obtain ⟨g, hg⟩ := X.exists_pointInclLE_eq_of_pow_eq_one (le_max_right v n) _ hpow
  exact ⟨g, by rw [← hg, X.pointsMkAdd_pointInclLE]⟩

section Proj

variable {R : Type} [CommRing R] {p h h'' : ℕ} {G : PDivisibleGroup R p h} {P : PDivisibleGroup R p h''}

noncomputable def proj (i : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (L : Type) [CommRing L] [Algebra R L] (v : ℕ)
    (x : P.Point L v) : G.Point L v :=
  Point.ofAlgHom ((Point.toAlgHom x).comp (i v : G.level v →ₐ[R] P.level v))

theorem proj_pointIncl (i : ∀ v : ℕ, G.level v →ₐc[R] P.level v)
    (hi : ∀ v : ℕ, (i v).comp (G.transition v) = (P.transition v).comp (i (v + 1)))
    (L : Type) [CommRing L] [Algebra R L] (v : ℕ) (x : P.Point L v) :
    proj i L (v + 1) (P.pointIncl L v x) = G.pointIncl L v (proj i L v x) := by
  refine Point.ext fun a => ?_
  show Point.toAlgHom x (P.transition v (i (v + 1) a)) = Point.toAlgHom x (i v (G.transition v a))
  congr 1
  exact (DFunLike.congr_fun (hi v) a).symm

theorem proj_pow (i : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (L : Type) [CommRing L] [Algebra R L] (v : ℕ)
    (hmul : ∀ x y : P.Point L v, proj i L v (x * y) = proj i L v x * proj i L v y)
    (x : P.Point L v) {k : ℕ} (hk : 1 ≤ k) : proj i L v (x ^ k) = proj i L v x ^ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ k hk ih => rw [pow_succ, pow_succ, hmul, ih]

end Proj

theorem exists_tateModule_lift {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime]
    (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') (P : PDivisibleGroup R p (h + h'))
    (iG : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (iH : ∀ v : ℕ, H.level v →ₐc[R] P.level v)
    (hiG : ∀ v : ℕ, (iG v).comp (G.transition v) = (P.transition v).comp (iG (v + 1)))
    (hiH : ∀ v : ℕ, (iH v).comp (H.transition v) = (P.transition v).comp (iH (v + 1)))
    (hpts : ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ),
          Function.Bijective (fun x : P.Point L v =>
            ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v),
             (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v))) ∧
          ∀ x y : P.Point L v,
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iG v : G.level v →ₐ[R] P.level v)) ∧
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iH v : H.level v →ₐ[R] P.level v)))
    (L : Type) [Field L] [Algebra R L]
    (y : TateModule p (G.Points L)) (z : TateModule p (H.Points L)) :
    ∃ x : TateModule p (P.Points L), ∀ n : ℕ, ∃ g : P.Point L n,
      P.pointsMkAdd L n (Additive.ofMul g) = (x : ℕ → P.Points L) n ∧
      G.pointsMkAdd L n (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom g).comp (iG n : G.level n →ₐ[R] P.level n)))) = (y : ℕ → G.Points L) n ∧
      H.pointsMkAdd L n (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom g).comp (iH n : H.level n →ₐ[R] P.level n)))) = (z : ℕ → H.Points L) n := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le

  have hbij : ∀ v : ℕ, Function.Bijective (fun x : P.Point L v => (proj iG L v x, proj iH L v x)) :=
    fun v => (hpts L v).1
  have hmulG : ∀ (v : ℕ) (x x' : P.Point L v), proj iG L v (x * x') = proj iG L v x * proj iG L v x' :=
    fun v x x' => ((hpts L v).2 x x').1
  have hmulH : ∀ (v : ℕ) (x x' : P.Point L v), proj iH L v (x * x') = proj iH L v x * proj iH L v x' :=
    fun v x x' => ((hpts L v).2 x x').2

  choose a ha using fun n => exists_point_of_smul_eq_zero G L ((y : ℕ → G.Points L) n) n (y.2 n).1
  choose b hb using fun n => exists_point_of_smul_eq_zero H L ((z : ℕ → H.Points L) n) n (z.2 n).1

  choose g hg using fun n => (hbij n).2 (a n, b n)
  have hgG : ∀ n, proj iG L n (g n) = a n := fun n => congrArg Prod.fst (hg n)
  have hgH : ∀ n, proj iH L n (g n) = b n := fun n => congrArg Prod.snd (hg n)

  have ha' : ∀ n, a (n + 1) ^ p = G.pointIncl L n (a n) := fun n =>
    Additive.ofMul.injective (G.pointsMkAdd_injective (L := L) (n + 1) (by
      rw [ofMul_pow, map_nsmul, ha, PDivisibleGroup.pointsMkAdd_pointIncl, ha, ← natCast_zsmul]
      exact (y.2 n).2))
  have hb' : ∀ n, b (n + 1) ^ p = H.pointIncl L n (b n) := fun n =>
    Additive.ofMul.injective (H.pointsMkAdd_injective (L := L) (n + 1) (by
      rw [ofMul_pow, map_nsmul, hb, PDivisibleGroup.pointsMkAdd_pointIncl, hb, ← natCast_zsmul]
      exact (z.2 n).2))

  have hcompat : ∀ n, g (n + 1) ^ p = P.pointIncl L n (g n) := fun n => by
    apply (hbij (n + 1)).1
    show (proj iG L (n + 1) (g (n + 1) ^ p), proj iH L (n + 1) (g (n + 1) ^ p)) =
      (proj iG L (n + 1) (P.pointIncl L n (g n)), proj iH L (n + 1) (P.pointIncl L n (g n)))
    rw [proj_pow iG L _ (hmulG _) _ hp1, proj_pow iH L _ (hmulH _) _ hp1, hgG, hgH, proj_pointIncl iG hiG,
      proj_pointIncl iH hiH, hgG, hgH, ha', hb']

  refine ⟨⟨fun n => P.pointsMkAdd L n (Additive.ofMul (g n)), fun n => ⟨?_, ?_⟩⟩, fun n => ⟨g n, rfl, ?_, ?_⟩⟩
  · rw [natCast_zsmul]
    exact P.nsmul_pointsMkAdd_eq_zero n (g n)
  · show ((p : ℕ) : ℤ) • P.pointsMkAdd L (n + 1) (Additive.ofMul (g (n + 1))) = P.pointsMkAdd L n (Additive.ofMul (g n))
    rw [natCast_zsmul, ← map_nsmul, ← ofMul_pow, hcompat, PDivisibleGroup.pointsMkAdd_pointIncl]
  · show G.pointsMkAdd L n (Additive.ofMul (proj iG L n (g n))) = _
    rw [hgG, ha]
  · show H.pointsMkAdd L n (Additive.ofMul (proj iH L n (g n))) = _
    rw [hgH, hb]

end PT

open PDivisibleGroup in
theorem solution
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h')
    (P : PDivisibleGroup R p (h + h'))
    (iG : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (iH : ∀ v : ℕ, H.level v →ₐc[R] P.level v)
    (hiG : ∀ v : ℕ, (iG v).comp (G.transition v) = (P.transition v).comp (iG (v + 1)))
    (hiH : ∀ v : ℕ, (iH v).comp (H.transition v) = (P.transition v).comp (iH (v + 1)))
    (hpts : ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ),
          Function.Bijective (fun x : P.Point L v =>
            ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v),
             (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v))) ∧
          ∀ x y : P.Point L v,
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iG v : G.level v →ₐ[R] P.level v)) ∧
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iH v : H.level v →ₐ[R] P.level v))) :
    ∀ (L : Type) [Field L] [Algebra R L],
        ∃ TP : TateModule p (P.Points L) ≃ₗ[ℤ_[p]] TateModule p (G.Points L) × TateModule p (H.Points L),
          (∀ (x : TateModule p (P.Points L)) (n w : ℕ) (g : P.Point L w),
            P.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → P.Points L) n →
            (((TP x).1 : TateModule p (G.Points L)) : ℕ → G.Points L) n =
              G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
                ((PDivisibleGroup.Point.toAlgHom g).comp (iG w : G.level w →ₐ[R] P.level w)))) ∧
            (((TP x).2 : TateModule p (H.Points L)) : ℕ → H.Points L) n =
              H.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
                ((PDivisibleGroup.Point.toAlgHom g).comp (iH w : H.level w →ₐ[R] P.level w))))) := by
  intro L _ _
  classical

  obtain ⟨TG, hTG, -⟩ := PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq p L G P iG hiG
  obtain ⟨TH, hTH, -⟩ := PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq p L H P iH hiH

  have hone : ∀ v : ℕ,
      (Point.ofAlgHom ((Point.toAlgHom (1 : P.Point L v)).comp (iG v : G.level v →ₐ[R] P.level v)) : G.Point L v) = 1 ∧
      (Point.ofAlgHom ((Point.toAlgHom (1 : P.Point L v)).comp (iH v : H.level v →ₐ[R] P.level v)) : H.Point L v) = 1 := by
    intro v
    obtain ⟨h1, h2⟩ := (hpts L v).2 1 1
    rw [one_mul] at h1 h2
    exact ⟨mul_eq_left.mp h1.symm, mul_eq_left.mp h2.symm⟩

  have hinj : Function.Injective (TG.prod TH) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx1 : TG x = 0 := congrArg Prod.fst hx
    have hx2 : TH x = 0 := congrArg Prod.snd hx
    apply Subtype.ext
    funext n
    obtain ⟨g, hg⟩ := PT.exists_point_of_smul_eq_zero P L ((x : ℕ → P.Points L) n) n (TateModule.torsion x n)
    have h1 := hTG x n n g hg
    have h2 := hTH x n n g hg
    rw [hx1] at h1
    rw [hx2] at h2

    have hg1 : (Point.ofAlgHom ((Point.toAlgHom g).comp (iG n : G.level n →ₐ[R] P.level n)) : G.Point L n) = 1 := by
      have : G.pointsMkAdd L n (Additive.ofMul
          (Point.ofAlgHom ((Point.toAlgHom g).comp (iG n : G.level n →ₐ[R] P.level n)) : G.Point L n)) =
          G.pointsMkAdd L n (Additive.ofMul 1) := by
        rw [← h1, ofMul_one, map_zero]; rfl
      exact Additive.ofMul.injective (G.pointsMkAdd_injective n this)
    have hg2 : (Point.ofAlgHom ((Point.toAlgHom g).comp (iH n : H.level n →ₐ[R] P.level n)) : H.Point L n) = 1 := by
      have : H.pointsMkAdd L n (Additive.ofMul
          (Point.ofAlgHom ((Point.toAlgHom g).comp (iH n : H.level n →ₐ[R] P.level n)) : H.Point L n)) =
          H.pointsMkAdd L n (Additive.ofMul 1) := by
        rw [← h2, ofMul_one, map_zero]; rfl
      exact Additive.ofMul.injective (H.pointsMkAdd_injective n this)
    have hgone : g = 1 := by
      apply (hpts L n).1.1
      simp only
      rw [hg1, hg2, (hone n).1, (hone n).2]
    rw [← hg, hgone, ofMul_one, map_zero]
    rfl

  have hsurj : Function.Surjective (TG.prod TH) := by
    rintro ⟨y, z⟩
    obtain ⟨x, hx⟩ := PT.exists_tateModule_lift G H P iG iH hiG hiH hpts L y z
    refine ⟨x, Prod.ext ?_ ?_⟩
    · apply Subtype.ext; funext n
      obtain ⟨g, hg, hgy, -⟩ := hx n
      rw [LinearMap.prod_apply]
      exact (hTG x n n g hg).trans hgy
    · apply Subtype.ext; funext n
      obtain ⟨g, hg, -, hgz⟩ := hx n
      rw [LinearMap.prod_apply]
      exact (hTH x n n g hg).trans hgz

  refine ⟨LinearEquiv.ofBijective (TG.prod TH) ⟨hinj, hsurj⟩, fun x n w g hg => ⟨?_, ?_⟩⟩
  · rw [LinearEquiv.ofBijective_apply, LinearMap.prod_apply]
    exact hTG x n w g hg
  · rw [LinearEquiv.ofBijective_apply, LinearMap.prod_apply]
    exact hTH x n w g hg

end S_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
end P2MW
export P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points (solution)
