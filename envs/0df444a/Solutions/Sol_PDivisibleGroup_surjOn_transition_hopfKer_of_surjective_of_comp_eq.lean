-- Prove2me | solution 1 for PDivisibleGroup.surjOn_transition_hopfKer_of_surjective_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2037685d-ab24-5e24-b5bd-398cd097a1de

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
import Theorems.Thm_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

namespace HQL3

section General

variable {R : Type} [CommRing R]
  {A A₀ C C₀ : Type} [CommRing A] [CommRing A₀] [CommRing C] [CommRing C₀]
  [Bialgebra R A] [Bialgebra R A₀] [Bialgebra R C] [Bialgebra R C₀]
  (τ : A →ₐc[R] A₀) (σ : C →ₐc[R] C₀) (μ : A →ₐc[R] C) (ρ : A₀ →ₐc[R] C₀)
  (hsq : σ.comp μ = ρ.comp τ)

include hsq in
theorem sq_apply (a : A) : σ (μ a) = ρ (τ a) := DFunLike.congr_fun hsq a

include hsq in

theorem map_hopfKer_le : (HopfAlgebra.hopfKer μ).map (τ : A →ₐ[R] A₀) ≤ HopfAlgebra.hopfKer ρ := by
  rintro _ ⟨a, ha, rfl⟩
  replace ha : HopfAlgebra.coaction μ a = a ⊗ₜ[R] 1 := (HopfAlgebra.mem_hopfKer_iff μ a).mp ha
  refine (HopfAlgebra.mem_hopfKer_iff ρ _).mpr ?_

  have key : ∀ x : A, HopfAlgebra.coaction ρ ((τ : A →ₐ[R] A₀) x) =
      Algebra.TensorProduct.map (τ : A →ₐ[R] A₀) (σ : C →ₐ[R] C₀) (HopfAlgebra.coaction μ x) := by
    intro x
    rw [HopfAlgebra.coaction_apply, HopfAlgebra.coaction_apply]
    have hΔ : Coalgebra.comul (R := R) ((τ : A →ₐ[R] A₀) x) =
        Algebra.TensorProduct.map (τ : A →ₐ[R] A₀) (τ : A →ₐ[R] A₀) (Coalgebra.comul (R := R) x) :=
      (CoalgHomClass.map_comp_comul_apply τ x).symm
    rw [hΔ]
    induction Coalgebra.comul (R := R) x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact (sq_apply τ σ μ ρ hsq b).symm
    | add y z hy hz => simp only [map_add, hy, hz]
  show HopfAlgebra.coaction ρ ((τ : A →ₐ[R] A₀) a) = (τ : A →ₐ[R] A₀) a ⊗ₜ[R] 1
  rw [key, ha, Algebra.TensorProduct.map_tmul, map_one]

end General

section Kernel

variable {R : Type} [CommRing R] {p : ℕ} {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
  (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
  (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v)) (v : ℕ)

include hπ hπt in

theorem ker_eq_map_ker :
    RingHom.ker (π v : G.level v →ₐ[R] T.level v) =
      Ideal.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v) (RingHom.ker (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, rfl⟩ := G.transition_surjective v z

    have h1 : π (v + 1) a ∈ RingHom.ker (T.transition v) := by
      rw [RingHom.mem_ker]
      show T.transition v (π (v + 1) a) = 0
      rw [show T.transition v (π (v + 1) a) = π v (G.transition v a) from DFunLike.congr_fun (hπt v) a]
      exact hz
    rw [T.ker_transition, ← PDivisibleGroup.Hopf.map_torsionIdeal_of_surjective (π (v + 1)) (hπ (v + 1)) (p ^ v),
      ← G.ker_transition] at h1
    obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))
      (hπ (v + 1))).mp h1
    have hab : a - b ∈ RingHom.ker (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1)) := by
      rw [RingHom.mem_ker, map_sub]
      change π (v + 1) a - π (v + 1) b = 0
      rw [sub_eq_zero]
      exact hba.symm
    have : G.transition v a = (G.transition v : G.level (v + 1) →ₐ[R] G.level v) (a - b) := by
      rw [map_sub]
      change _ = G.transition v a - G.transition v b
      rw [show G.transition v b = 0 from hb, sub_zero]
    rw [this]
    exact Ideal.mem_map_of_mem _ hab
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change π v (G.transition v y) = 0
    rw [← show T.transition v (π (v + 1) y) = π v (G.transition v y) from DFunLike.congr_fun (hπt v) y,
      show π (v + 1) y = 0 from hy, map_zero]

end Kernel

section Residue

variable {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {h t : ℕ}
  (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
  (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
  (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v)) (v : ℕ)

local notation "k" => ResidueField R

noncomputable abbrev bc {X Y : Type} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    k ⊗[R] X →ₐc[k] k ⊗[R] Y :=
  Bialgebra.TensorProduct.map (BialgHom.id k k) f

theorem bc_toAlgHom {X Y : Type} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    (bc f : k ⊗[R] X →ₐ[k] k ⊗[R] Y) = Algebra.TensorProduct.map (AlgHom.id k k) (f : X →ₐ[R] Y) := by
  ext x <;> rfl

theorem bc_surjective {X Y : Type} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y)
    (hf : Function.Surjective f) : Function.Surjective (bc f) := by
  change Function.Surjective ((bc f : k ⊗[R] X →ₐ[k] k ⊗[R] Y))
  rw [bc_toAlgHom]
  exact Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hf

theorem ker_bc {X Y : Type} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y)
    (hf : Function.Surjective f) :
    RingHom.ker (bc f : k ⊗[R] X →ₐ[k] k ⊗[R] Y) =
      (RingHom.ker (f : X →ₐ[R] Y)).map (Algebra.TensorProduct.includeRight : X →ₐ[R] k ⊗[R] X) := by
  rw [bc_toAlgHom]
  have := Algebra.TensorProduct.lTensor_ker (A := k) (f : X →ₐ[R] Y) hf
  rw [← this]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have : Algebra.TensorProduct.map (AlgHom.id k k) (f : X →ₐ[R] Y) x = Algebra.TensorProduct.map (AlgHom.id R k) (f : X →ₐ[R] Y) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s a => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [this]

theorem bc_comp_includeRight {X Y : Type} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    (bc f : k ⊗[R] X →ₐ[k] k ⊗[R] Y).toRingHom.comp (Algebra.TensorProduct.includeRight : X →ₐ[R] k ⊗[R] X).toRingHom =
      (Algebra.TensorProduct.includeRight : Y →ₐ[R] k ⊗[R] Y).toRingHom.comp (f : X →ₐ[R] Y).toRingHom := by
  ext x
  rfl

include hπ hπt in

theorem map_hopfKer_bc_eq :
    (HopfAlgebra.hopfKer (bc (π (v + 1)))).map (bc (G.transition v) : k ⊗[R] G.level (v + 1) →ₐ[k] k ⊗[R] G.level v) =
      HopfAlgebra.hopfKer (bc (π v)) := by
  refine HopfAlgebra.map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker k
    (bc (G.transition v)) (bc (π (v + 1))) (bc (π v))
    (bc_surjective _ (G.transition_surjective v)) (bc_surjective _ (hπ (v + 1))) (bc_surjective _ (hπ v)) ?_

  rw [ker_bc _ (hπ v), ker_bc _ (hπ (v + 1)), ker_eq_map_ker G T π hπ hπt v]
  change Ideal.map (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] k ⊗[R] G.level v).toRingHom
      (Ideal.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v).toRingHom _) =
    Ideal.map (bc (G.transition v) : k ⊗[R] G.level (v + 1) →ₐ[k] k ⊗[R] G.level v).toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight : G.level (v + 1) →ₐ[R] k ⊗[R] G.level (v + 1)).toRingHom _)
  rw [Ideal.map_map, Ideal.map_map, bc_comp_includeRight]

end Residue

section Nakayama

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem inf_smul_top_le {V : Type} [AddCommGroup V] [Module R V] (N : Submodule R V)
    (r : V →ₗ[R] N) (hr : ∀ n : N, r n = n) (I : Ideal R) :
    ∀ x ∈ N, x ∈ I • (⊤ : Submodule R V) → x ∈ (I • (⊤ : Submodule R N)).map N.subtype := by
  intro x hxN hxI
  refine ⟨r x, ?_, by rw [hr ⟨x, hxN⟩]; rfl⟩

  have : Submodule.map r (I • ⊤) ≤ I • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨x, hxI, rfl⟩

theorem mem_sup_of_one_tmul_mem_baseChange {V : Type} [AddCommGroup V] [Module R V] (Q : Submodule R V) (n : V)
    (hn : (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] n ∈ Q.baseChange (R ⧸ maximalIdeal R)) :
    n ∈ Q ⊔ maximalIdeal R • (⊤ : Submodule R V) := by

  have himg : ∀ z : (R ⧸ maximalIdeal R) ⊗[R] ↥Q,
      TensorProduct.quotTensorEquivQuotSMul V (maximalIdeal R) ((Q.subtype.baseChange (R ⧸ maximalIdeal R)) z) ∈
      Q.map (maximalIdeal R • (⊤ : Submodule R V)).mkQ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | tmul c q =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
      exact ⟨r • (q : V), Q.smul_mem r q.2, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  obtain ⟨z, hz⟩ := hn
  have h2 := himg z
  rw [hz, ← map_one (Ideal.Quotient.mk (maximalIdeal R)), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul] at h2
  have h3 : n ∈ Submodule.comap (maximalIdeal R • (⊤ : Submodule R V)).mkQ (Q.map (maximalIdeal R • (⊤ : Submodule R V)).mkQ) := h2
  rw [Submodule.comap_map_mkQ] at h3
  rwa [sup_comm]

end Nakayama

section Main

variable {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {h t : ℕ}
  (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
  (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
  (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v)) (v : ℕ)

local notation "k" => ResidueField R

include hπ hπt in

theorem main :
    Set.SurjOn (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v)) := by
  classical

  let τ : G.level (v + 1) →ₐ[R] G.level v := (G.transition v : G.level (v + 1) →ₐ[R] G.level v)
  let N : Subalgebra R (G.level v) := HopfAlgebra.hopfKer (π v)
  let M : Subalgebra R (G.level v) := (HopfAlgebra.hopfKer (π (v + 1))).map τ
  have hMN : M ≤ N := map_hopfKer_le (G.transition v) (T.transition v) (π (v + 1)) (π v) (hπt v)

  suffices hNM : Subalgebra.toSubmodule N ≤ Subalgebra.toSubmodule M by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (show y ∈ M from hNM hy)
    exact ⟨a, ha, rfl⟩

  obtain ⟨⟨r, hr⟩, hNfin, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (π v) (hπ v)
  haveI := hNfin
  let rR : G.level v →ₗ[R] ↥N := r.restrictScalars R
  have hrR : ∀ n : ↥N, rR n = n := hr
  have hfg : (Subalgebra.toSubmodule N).FG := (Submodule.fg_top _).mp (Module.finite_def.mp hNfin)

  refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) fun n hn => ?_

  have hbcN := HopfAlgebra.baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective (π v) (hπ v)
  have hbcK := HopfAlgebra.baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective
    (π (v + 1)) (hπ (v + 1))
  have h1 : (1 : k) ⊗ₜ[R] n ∈ Subalgebra.toSubmodule (HopfAlgebra.hopfKer (bc (π v))) := by
    rw [← hbcN]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hn
  rw [← map_hopfKer_bc_eq G T π hπ hπt v, Subalgebra.map_toSubmodule, ← hbcK] at h1
  obtain ⟨w, hw, hwn⟩ := h1
  have h2 : (1 : k) ⊗ₜ[R] n ∈ (Subalgebra.toSubmodule M).baseChange k := by
    rw [← hwn]
    obtain ⟨z, rfl⟩ := hw
    clear hwn
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | tmul c q =>
      rw [LinearMap.baseChange_tmul]
      change (bc (G.transition v)) (c ⊗ₜ[R] (q : G.level (v + 1))) ∈ _
      rw [Bialgebra.TensorProduct.map_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ ⟨q, q.2, rfl⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy

  have h3 := mem_sup_of_one_tmul_mem_baseChange (Subalgebra.toSubmodule M) n h2
  obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.mp h3
  have hxN : x ∈ N := by
    have : m + x - m ∈ N := N.sub_mem hn (hMN hm)
    rwa [add_sub_cancel_left] at this
  have hx' := inf_smul_top_le (Subalgebra.toSubmodule N) rR hrR (maximalIdeal R) x hxN hx
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at hx'
  exact Submodule.add_mem_sup hm hx'

end Main

end HQL3

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v))
    (v : ℕ) :
    Set.SurjOn (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v)) :=
  HQL3.main G T π hπ hπt v

end S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq
end P2MW
export P2MW.S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq (solution)
