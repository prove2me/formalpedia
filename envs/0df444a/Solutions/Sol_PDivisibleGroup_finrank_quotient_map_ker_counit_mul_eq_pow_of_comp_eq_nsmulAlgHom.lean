-- Prove2me | solution 1 for PDivisibleGroup.finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/42f712af-c7c5-5df1-a5c4-956d9cc8d0c6

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

universe u v w

open PDivisibleGroup.Hopf

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.nsmulAlgHom Hopf.torsionIdeal transition level Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal"
p2m_open "PDivisibleGroup"

namespace KerCountField

section Generic

variable {R : Type*} [CommRing R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

private theorem map_augIdeal_le [Bialgebra R A] [Bialgebra R B] (φ : B →ₐc[R] A) :
    (augIdeal R B).map (φ : B →ₐ[R] A) ≤ augIdeal R A := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, mem_augIdeal_iff]
  change Coalgebra.counit (R := R) (φ b) = 0
  rw [CoalgHomClass.counit_comp_apply]
  exact (mem_augIdeal_iff R B b).1 hb

private theorem map_augIdeal_eq_of_surjective [Bialgebra R A] [Bialgebra R B] (φ : B →ₐc[R] A)
    (hφ : Function.Surjective φ) :
    (augIdeal R B).map (φ : B →ₐ[R] A) = augIdeal R A := by
  refine le_antisymm (map_augIdeal_le φ) ?_
  intro a ha
  have hφ' : Function.Surjective (φ : B →ₐ[R] A) := hφ
  obtain ⟨b, rfl⟩ := hφ' a
  have hb : b - algebraMap R B (Coalgebra.counit (R := R) b) ∈ augIdeal R B :=
    sub_algebraMap_counit_mem_augIdeal R B b
  have hεb : Coalgebra.counit (R := R) b = 0 := by
    have ha' := (mem_augIdeal_iff R A _).1 ha
    change Coalgebra.counit (R := R) (φ b) = 0 at ha'
    rwa [CoalgHomClass.counit_comp_apply] at ha'
  rw [hεb, map_zero, sub_zero] at hb
  exact Ideal.mem_map_of_mem _ hb

private theorem ideal_map_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (I : Ideal A) :
    I.map (g.comp f) = (I.map f).map g :=
  (Ideal.map_map (f : A →+* B) (g : B →+* C)).symm

private theorem nsmulAlgHom_comp_nsmulAlgHom [Bialgebra R A] (m n : ℕ) :
    (nsmulAlgHom R A m).comp (nsmulAlgHom R A n) = nsmulAlgHom R A (m * n) := by
  rw [nsmulAlgHom_mul R A m n, toConv_pow_eq_toConv_comp_nsmulAlgHom (nsmulAlgHom R A m) n]

private theorem torsionIdeal_mul_le [Bialgebra R A] (m n : ℕ) :
    torsionIdeal R A (m * n) ≤ torsionIdeal R A m := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← nsmulAlgHom_comp_nsmulAlgHom, AlgHom.comp_apply]
  exact nsmulAlgHom_mem_torsionIdeal R A (nsmulAlgHom_mem_augIdeal R A ha n) m

private noncomputable def nsmulBialgHom (R : Type*) [CommRing R] (A : Type*) [CommRing A]
    [Bialgebra R A] [Coalgebra.IsCocomm R A] (n : ℕ) : A →ₐc[R] A :=
  ((WithConv.toConv (BialgHom.id R A)) ^ n).ofConv

private theorem toAlgHom_nsmulBialgHom [Bialgebra R A] [Coalgebra.IsCocomm R A] (n : ℕ) :
    (nsmulBialgHom R A n : A →ₐ[R] A) = nsmulAlgHom R A n := by
  have h := congrArg WithConv.ofConv (BialgHom.toAlgHom_convPow (WithConv.toConv (BialgHom.id R A)) n)
  exact h

private theorem ker_comp_of_injective [Algebra R A] [Algebra R B] [Algebra R C]
    (π : A →ₐ[R] B) (ι : B →ₐ[R] C) (hι : Function.Injective ι) :
    RingHom.ker (ι.comp π) = RingHom.ker π := by
  ext a
  simp only [RingHom.mem_ker, AlgHom.comp_apply]
  exact map_eq_zero_iff ι hι

end Generic

section Field

variable {κ : Type*} [Field κ] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra κ A] [Algebra κ B] [Algebra κ C]

private theorem finrank_quotient_map_of_surjective (π : B →ₐ[κ] C) (hπ : Function.Surjective π)
    (J : Ideal B) (hJ : RingHom.ker π ≤ J) :
    Module.finrank κ (C ⧸ J.map π) = Module.finrank κ (B ⧸ J) := by
  set q : B →ₐ[κ] C ⧸ J.map π := (Ideal.Quotient.mkₐ κ (J.map π)).comp π with hq_def
  have hq : Function.Surjective q := (Ideal.Quotient.mkₐ_surjective κ _).comp hπ
  have hker : RingHom.ker q = J := by
    have h1 : RingHom.ker q = Ideal.comap π (J.map π) := by
      ext b
      simp only [RingHom.mem_ker, Ideal.mem_comap, hq_def, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
    rw [h1, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hJ]
  exact (((Ideal.quotientEquivAlgOfEq κ hker).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective hq)).toLinearEquiv.finrank_eq).symm

private theorem ideal_eq_of_le_of_finrank_quotient_eq [Module.Finite κ B] {I J : Ideal B}
    (hIJ : I ≤ J) (hfin : Module.finrank κ (B ⧸ I) = Module.finrank κ (B ⧸ J)) : I = J := by
  have key : ∀ K : Ideal B,
      Module.finrank κ (B ⧸ K) + Module.finrank κ ↥(K.restrictScalars κ) = Module.finrank κ B := by
    intro K
    rw [← (Submodule.Quotient.restrictScalarsEquiv κ K).finrank_eq]
    exact Submodule.finrank_quotient_add_finrank _
  have hI := key I
  have hJ := key J
  have hdim : Module.finrank κ ↥(I.restrictScalars κ) = Module.finrank κ ↥(J.restrictScalars κ) := by
    omega
  exact Submodule.restrictScalars_injective κ B B
    (Submodule.eq_of_le_of_finrank_eq (fun x hx => hIJ hx) hdim)

private theorem finrank_range_comp_of_injective (ψ : A →ₐ[κ] B) (ι : B →ₐ[κ] C)
    (hι : Function.Injective ι) :
    Module.finrank κ ↥(ι.comp ψ).range = Module.finrank κ ↥ψ.range := by
  rw [AlgHom.range_comp]
  exact (Subalgebra.equivMapOfInjective ψ.range ι hι).toLinearEquiv.finrank_eq.symm

private theorem finrank_eq_finrank_range_of_comp_eq (π : A →ₐ[κ] B) (ι : B →ₐ[κ] C)
    (hπ : Function.Surjective π) (hι : Function.Injective ι) (f : A →ₐ[κ] C) (hf : ι.comp π = f) :
    Module.finrank κ B = Module.finrank κ ↥f.range := by
  rw [← hf, finrank_range_comp_of_injective π ι hι, (AlgHom.range_eq_top π).2 hπ]
  exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq.symm

end Field

section Tower

variable (κ : Type u) [Field κ] (p : ℕ) (h : ℕ)

private theorem finrank_quotient_torsionIdeal
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (N a b : ℕ) (hN : N = a + b) :
    Module.finrank κ (L N ⧸ torsionIdeal κ (L N) (p ^ b)) = p ^ (b * h) := by
  obtain ⟨T, -, -, -, -, -, hfree⟩ :=
    exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L t ht hrankL hkerL
  subst hN
  exact (hfree a b).2

private theorem nsmulAlgHom_level_apply
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (N : ℕ) (a : L N) :
    nsmulAlgHom κ (L N) (p ^ N) a = algebraMap κ (L N) (Coalgebra.counit (R := κ) a) := by
  obtain ⟨T, -, -, -, -, hkill, -⟩ :=
    exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L t ht hrankL hkerL
  rw [hkill N]
  rfl

private theorem finrank_range_nsmulAlgHom [Fact p.Prime]
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (N a b : ℕ) (hN : N = a + b) :
    Module.finrank κ ↥(nsmulAlgHom κ (L N) (p ^ b)).range = p ^ (a * h) := by
  have hq := finrank_quotient_torsionIdeal κ p h L t ht hrankL hkerL N a b hN
  have himc := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range κ
    (nsmulBialgHom κ (L N) (p ^ b))
  rw [toAlgHom_nsmulBialgHom] at himc
  change Module.finrank κ (L N) =
    Module.finrank κ (L N ⧸ torsionIdeal κ (L N) (p ^ b)) * _ at himc
  rw [hq, hrankL] at himc
  have hp : 0 < p ^ (b * h) := pow_pos (Nat.Prime.pos Fact.out) _
  refine (Nat.eq_of_mul_eq_mul_left hp ?_).symm
  rw [← himc, hN]
  ring

private theorem torsionIdeal_eq_ker_nsmulAlgHom [Fact p.Prime]
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (N a b : ℕ) (hN : N = a + b) :
    torsionIdeal κ (L N) (p ^ a) = RingHom.ker (nsmulAlgHom κ (L N) (p ^ b)) := by
  refine ideal_eq_of_le_of_finrank_quotient_eq (κ := κ) ?_ ?_
  · rw [torsionIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, nsmulAlgHom_comp_nsmulAlgHom,
      ← pow_add, Nat.add_comm b a, ← hN,
      nsmulAlgHom_level_apply κ p h L t ht hrankL hkerL N x, (mem_augIdeal_iff κ (L N) x).1 hx,
      map_zero]
  · rw [finrank_quotient_torsionIdeal κ p h L t ht hrankL hkerL N b a (by omega)]
    have e := (Ideal.quotientEquivAlgOfEq κ
      (AlgHom.ker_rangeRestrict (nsmulAlgHom κ (L N) (p ^ b))).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (AlgHom.rangeRestrict_surjective (nsmulAlgHom κ (L N) (p ^ b))))
    rw [e.toLinearEquiv.finrank_eq]
    exact (finrank_range_nsmulAlgHom κ p h L t ht hrankL hkerL N a b hN).symm

private theorem finrank_kerAlgebra_eq
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra κ (L' v)]
    [∀ v, Coalgebra.IsCocomm κ (L' v)] [∀ v, Module.Free κ (L' v)] [∀ v, Module.Finite κ (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[κ] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank κ (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = torsionIdeal κ (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[κ] L v) (hf : ∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1)))
    (g : ∀ v, L v →ₐc[κ] L' v) (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[κ] L u).comp (g u : L u →ₐ[κ] L' u) =
      nsmulAlgHom κ (L u) (p ^ w))
    (n d : ℕ) (hn : w ≤ n) :
    Module.finrank κ (L (n + d) ⧸ Ideal.map (f (n + d) : L' (n + d) →ₐ[κ] L (n + d))
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' (n + d))))) =
      Module.finrank κ (L n ⧸ Ideal.map (f n : L' n →ₐ[κ] L n)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' n)))) := by
  obtain ⟨T, hT0, hTs, hTsurj, hTker, -, -⟩ :=
    exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L t ht hrankL hkerL
  obtain ⟨T', hT0', hTs', hTsurj', -, -, -⟩ :=
    exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L' t' ht' hrankL' hkerL'

  have hcompat : ∀ d, (f n).comp (T' n d) = (T n d).comp (f (n + d)) := by
    intro d
    induction d with
    | zero =>
      rw [hT0, hT0']
      ext x
      rfl
    | succ d ih =>
      ext x
      have h1 : (T' n (d + 1)) x = T' n d (t' (n + d) x) := by rw [hTs']; rfl
      have h2 : (T n (d + 1)) (f (n + (d + 1)) x) = T n d (t (n + d) (f (n + d + 1) x)) := by
        rw [hTs]; rfl
      have h3 : f (n + d) (t' (n + d) x) = t (n + d) (f (n + d + 1) x) :=
        DFunLike.congr_fun (hf (n + d)) x
      have h4 : f n (T' n d (t' (n + d) x)) = T n d (f (n + d) (t' (n + d) x)) :=
        DFunLike.congr_fun ih (t' (n + d) x)
      rw [BialgHom.comp_apply, BialgHom.comp_apply, h1, h2, h4, h3]
  have hcompat' : ((T n d : L (n + d) →ₐ[κ] L n).comp (f (n + d) : L' (n + d) →ₐ[κ] L (n + d))) =
      (f n : L' n →ₐ[κ] L n).comp (T' n d : L' (n + d) →ₐ[κ] L' n) :=
    AlgHom.ext fun x => (DFunLike.congr_fun (hcompat d) x).symm
  have hsurjT : Function.Surjective (T n d : L (n + d) →ₐ[κ] L n) := hTsurj n d

  have hJ : (Ideal.map (f (n + d) : L' (n + d) →ₐ[κ] L (n + d))
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' (n + d))))).map (T n d : L (n + d) →ₐ[κ] L n) =
      Ideal.map (f n : L' n →ₐ[κ] L n) (RingHom.ker (Bialgebra.counitAlgHom κ (L' n))) := by
    rw [← ideal_map_comp, hcompat', ideal_map_comp]
    exact congrArg _ (map_augIdeal_eq_of_surjective (T' n d) (hTsurj' n d))

  have hker : RingHom.ker (T n d : L (n + d) →ₐ[κ] L n) ≤
      Ideal.map (f (n + d) : L' (n + d) →ₐ[κ] L (n + d))
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' (n + d)))) := by
    have hpw : p ^ n = p ^ w * p ^ (n - w) := by rw [← pow_add, Nat.add_sub_cancel' hn]
    calc RingHom.ker (T n d : L (n + d) →ₐ[κ] L n)
        = torsionIdeal κ (L (n + d)) (p ^ n) := hTker n d
      _ ≤ torsionIdeal κ (L (n + d)) (p ^ w) := by rw [hpw]; exact torsionIdeal_mul_le _ _
      _ = (augIdeal κ (L (n + d))).map ((f (n + d) : L' (n + d) →ₐ[κ] L (n + d)).comp
            (g (n + d) : L (n + d) →ₐ[κ] L' (n + d))) := by rw [hgf]; rfl
      _ = ((augIdeal κ (L (n + d))).map (g (n + d) : L (n + d) →ₐ[κ] L' (n + d))).map
            (f (n + d) : L' (n + d) →ₐ[κ] L (n + d)) := ideal_map_comp _ _ _
      _ ≤ _ := Ideal.map_mono (map_augIdeal_le (g (n + d)))
  rw [← finrank_quotient_map_of_surjective _ hsurjT _ hker, hJ]

private theorem count_level [Fact p.Prime]
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = torsionIdeal κ (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra κ (L' v)]
    [∀ v, Coalgebra.IsCocomm κ (L' v)] [∀ v, Module.Free κ (L' v)] [∀ v, Module.Finite κ (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[κ] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank κ (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = torsionIdeal κ (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[κ] L v) (g : ∀ v, L v →ₐc[κ] L' v) (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[κ] L u).comp (g u : L u →ₐ[κ] L' u) =
      nsmulAlgHom κ (L u) (p ^ w))
    (hfg : ∀ u, (g u : L u →ₐ[κ] L' u).comp (f u : L' u →ₐ[κ] L u) =
      nsmulAlgHom κ (L' u) (p ^ w))
    (N m : ℕ) (hN : N = m + w) (hm : w ≤ m) :
    Module.finrank κ (L N ⧸ Ideal.map (f N : L' N →ₐ[κ] L N)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' N)))) *
      Module.finrank κ (L' N ⧸ Ideal.map (g N : L N →ₐ[κ] L' N)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L N)))) = p ^ (w * h) := by

  obtain ⟨Q, _, _, _, _, π, ι, hπ, hι, hιπ, -, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem (f N)
  have hιπ' : (ι : Q →ₐ[κ] L N).comp (π : L' N →ₐ[κ] Q) = (f N : L' N →ₐ[κ] L N) :=
    AlgHom.ext fun x => by rw [← hιπ]; rfl
  have hπ' : Function.Surjective (π : L' N →ₐ[κ] Q) := hπ
  have hι' : Function.Injective (ι : Q →ₐ[κ] L N) := hι

  have h1 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range κ (f N)

  have h4 := finrank_eq_finrank_range_of_comp_eq _ _ hπ' hι' _ hιπ'

  have h3 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range κ (π.comp (g N))
  have hcomp : ((π.comp (g N) : L N →ₐc[κ] Q) : L N →ₐ[κ] Q) =
      (π : L' N →ₐ[κ] Q).comp (g N : L N →ₐ[κ] L' N) := rfl
  rw [hcomp] at h3

  have hker : RingHom.ker (π : L' N →ₐ[κ] Q) ≤
      Ideal.map (g N : L N →ₐ[κ] L' N) (RingHom.ker (Bialgebra.counitAlgHom κ (L N))) := by
    have hpw : p ^ m = p ^ w * p ^ (m - w) := by rw [← pow_add, Nat.add_sub_cancel' hm]
    calc RingHom.ker (π : L' N →ₐ[κ] Q)
        = RingHom.ker (f N : L' N →ₐ[κ] L N) := by rw [← ker_comp_of_injective _ _ hι', hιπ']
      _ ≤ RingHom.ker ((g N : L N →ₐ[κ] L' N).comp (f N : L' N →ₐ[κ] L N)) := by
          intro x hx
          rw [RingHom.mem_ker] at hx
          rw [RingHom.mem_ker, AlgHom.comp_apply, hx, map_zero]
      _ = RingHom.ker (nsmulAlgHom κ (L' N) (p ^ w)) := by rw [hfg]
      _ = torsionIdeal κ (L' N) (p ^ m) :=
          (torsionIdeal_eq_ker_nsmulAlgHom κ p h L' t' ht' hrankL' hkerL' N m w hN).symm
      _ ≤ torsionIdeal κ (L' N) (p ^ w) := by rw [hpw]; exact torsionIdeal_mul_le _ _
      _ = (augIdeal κ (L' N)).map ((g N : L N →ₐ[κ] L' N).comp (f N : L' N →ₐ[κ] L N)) := by
          rw [hfg]; rfl
      _ = ((augIdeal κ (L' N)).map (f N : L' N →ₐ[κ] L N)).map (g N : L N →ₐ[κ] L' N) :=
          ideal_map_comp _ _ _
      _ ≤ _ := Ideal.map_mono (map_augIdeal_le (f N))
  have h5 : Module.finrank κ (Q ⧸ Ideal.map ((π : L' N →ₐ[κ] Q).comp (g N : L N →ₐ[κ] L' N))
        (RingHom.ker (Bialgebra.counitAlgHom κ (L N)))) =
      Module.finrank κ (L' N ⧸ Ideal.map (g N : L N →ₐ[κ] L' N)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L N)))) := by
    rw [ideal_map_comp]
    exact finrank_quotient_map_of_surjective _ hπ' _ hker

  have h6 : Module.finrank κ ↥((π : L' N →ₐ[κ] Q).comp (g N : L N →ₐ[κ] L' N)).range =
      p ^ (m * h) := by
    rw [← finrank_range_comp_of_injective _ _ hι', ← AlgHom.comp_assoc, hιπ', hgf]
    exact finrank_range_nsmulAlgHom κ p h L t ht hrankL hkerL N m w hN
  rw [h5, h6] at h3
  rw [hrankL, ← h4, h3] at h1

  have hp : 0 < p ^ (m * h) := pow_pos (Nat.Prime.pos Fact.out) _
  refine Nat.eq_of_mul_eq_mul_left hp ?_
  calc p ^ (m * h) * (_ * _) = _ := by rw [mul_comm, mul_assoc]
    _ = p ^ (N * h) := h1.symm
    _ = p ^ (m * h) * p ^ (w * h) := by rw [hN]; ring

end Tower

end KerCountField

end PDivisibleGroup

open PDivisibleGroup.KerCountField in
theorem solution
    (κ : Type u) [Field κ] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal κ (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra κ (L' v)]
    [∀ v, Coalgebra.IsCocomm κ (L' v)] [∀ v, Module.Free κ (L' v)] [∀ v, Module.Finite κ (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[κ] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank κ (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal κ (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[κ] L v) (hf : ∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1)))
    (g : ∀ v, L v →ₐc[κ] L' v) (hg : ∀ u, (g u).comp (t u) = (t' u).comp (g (u + 1)))
    (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[κ] L u).comp (g u : L u →ₐ[κ] L' u) =
      PDivisibleGroup.Hopf.nsmulAlgHom κ (L u) (p ^ w))
    (hfg : ∀ u, (g u : L u →ₐ[κ] L' u).comp (f u : L' u →ₐ[κ] L u) =
      PDivisibleGroup.Hopf.nsmulAlgHom κ (L' u) (p ^ w))
    (v : ℕ) (hv : w ≤ v) :
    Module.finrank κ (L v ⧸ Ideal.map (f v : L' v →ₐ[κ] L v)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' v)))) *
      Module.finrank κ (L' v ⧸ Ideal.map (g v : L v →ₐ[κ] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L v)))) = p ^ (w * h) := by
  rw [← finrank_kerAlgebra_eq κ p h L t ht hrankL hkerL L' t' ht' hrankL' hkerL' f hf g w hgf v w hv,
    ← finrank_kerAlgebra_eq κ p h L' t' ht' hrankL' hkerL' L t ht hrankL hkerL g hg f w hfg v w hv]
  exact count_level κ p h L t ht hrankL hkerL L' t' ht' hrankL' hkerL' f g w hgf hfg (v + w) v rfl hv

end S_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
end P2MW
export P2MW.S_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom (solution)
