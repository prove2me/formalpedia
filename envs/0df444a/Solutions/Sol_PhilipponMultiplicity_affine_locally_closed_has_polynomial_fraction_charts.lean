-- Prove2me | solution 1 for PhilipponMultiplicity.affine_locally_closed_has_polynomial_fraction_charts
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T20:49:14.523723+00:00
-- url     : https://prove2.me/submissions/9a9ce468-8c4e-40fe-bdb4-2eba57bd06d5

import Mathlib

section
-- Included implementation: Solutions.PhilipponAffineClosedPoints

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial
open Topology

variable {K : Type*} [Field K] {σ τ : Type*}

/-- The ordinary Zariski topology on an affine algebraic zero set, induced by its
evaluation ideals in the polynomial prime spectrum. -/
@[instance_reducible] def locusTopology (I : Ideal (MvPolynomial σ K)) :
    TopologicalSpace (zeroLocus K I) :=
  TopologicalSpace.induced (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
    inferInstance

theorem nonzero_sets_basis (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    TopologicalSpace.IsTopologicalBasis
      (Set.range (fun P : MvPolynomial σ K => {x : zeroLocus K I | aeval x.val P ≠ 0})) := by
  let _ := locusTopology I
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
  have hpre (P : MvPolynomial σ K) :
      (fun x : zeroLocus K I => pointToPoint (k := K) x.val) ⁻¹'
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (MvPolynomial σ K))) =
      {x : zeroLocus K I | aeval x.val P ≠ 0} := by
    ext x
    change (P ∉ vanishingIdeal K {x.val}) ↔ aeval x.val P ≠ 0
    rw [mem_vanishingIdeal_singleton_iff]
  simpa only [← Set.range_comp, Function.comp_def, hpre] using hb


end PhilipponMultiplicity.AffineClosedPoints
end
end

section
-- Included implementation: Solutions.PhilipponAffineClosedSubsets
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity.AffineClosedSubsets
variable {K : Type*} [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (C : Set (zeroLocus K I))

def ideal : Ideal (MvPolynomial σ K) := vanishingIdeal K (Subtype.val '' C)

theorem ideal_isRadical : (ideal I C).IsRadical := by
  intro P ⟨n, hn⟩ v hv
  have h := hn v hv
  rw [map_pow] at h
  by_contra hn
  exact pow_ne_zero n hn h

theorem le_ideal : I ≤ ideal I C := by
  intro P hP v hv
  obtain ⟨x, _, rfl⟩ := hv
  exact x.property P hP

def restrict (v : zeroLocus K (ideal I C)) : zeroLocus K I :=
  ⟨v.val, fun P hP => v.property P (le_ideal I C hP)⟩

theorem restrict_mem
    (hC : @IsClosed _ (AffineClosedPoints.locusTopology I) C)
    (v : zeroLocus K (ideal I C)) : restrict I C v ∈ C := by
  letI := AffineClosedPoints.locusTopology I
  by_contra hv
  obtain ⟨_, ⟨P, rfl⟩, hxP, hPC⟩ :=
    (AffineClosedPoints.nonzero_sets_basis I).exists_subset_of_mem_open hv hC.isOpen_compl
  have hP : P ∈ ideal I C := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hw
    by_contra hn
    exact hPC hn hy
  exact hxP (v.property P hP)

def toLocus (x : C) : zeroLocus K (ideal I C) :=
  ⟨x.val.val, fun P hP => hP x.val.val ⟨x.val, x.property, rfl⟩⟩

def fromLocus (hC : @IsClosed _ (AffineClosedPoints.locusTopology I) C)
    (v : zeroLocus K (ideal I C)) : C :=
  ⟨restrict I C v, restrict_mem I C hC v⟩

def equiv (hC : @IsClosed _ (AffineClosedPoints.locusTopology I) C) :
    C ≃ zeroLocus K (ideal I C) where
  toFun := toLocus I C
  invFun := fromLocus I C hC
  left_inv _ := rfl
  right_inv _ := rfl

theorem toLocus_continuous :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I C)
    Continuous (toLocus I C) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I C)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal I C)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  exact ((AffineClosedPoints.nonzero_sets_basis I).isOpen (Set.mem_range_self P)).preimage
    continuous_subtype_val

theorem fromLocus_continuous
    (hC : @IsClosed _ (AffineClosedPoints.locusTopology I) C) :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I C)
    Continuous (fromLocus I C hC) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I C)
  apply Continuous.subtype_mk
  apply (AffineClosedPoints.nonzero_sets_basis I).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  exact (AffineClosedPoints.nonzero_sets_basis (ideal I C)).isOpen (Set.mem_range_self P)

/-- A closed subset of an affine zero set is the affine zero set of its
vanishing ideal, with exactly the original point-set topology. -/
def homeomorph (hC : @IsClosed _ (AffineClosedPoints.locusTopology I) C) :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I C)
    C ≃ₜ zeroLocus K (ideal I C) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I C)
  exact { equiv I C hC with
    continuous_toFun := toLocus_continuous I C
    continuous_invFun := fromLocus_continuous I C hC }

end PhilipponMultiplicity.AffineClosedSubsets

end
end

section
-- Included implementation: Solutions.PhilipponAffinePrincipalGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity.AffinePrincipalGraph
variable {K : Type*} [Field K] {σ : Type*}

/-- Substituting the inverse of a polynomial for one extra variable gives
a fraction whose denominator is a power of that polynomial. -/
theorem inverse_substitution_fraction (Q : MvPolynomial σ K)
    (P : MvPolynomial (Option σ) K) :
    ∃ A : MvPolynomial σ K, ∃ n : ℕ, ∀ v : σ → K, aeval v Q ≠ 0 →
      aeval (fun t => t.elim ((aeval v Q)⁻¹) v) P = aeval v A / (aeval v Q)^n := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp⟩
  | add P R hP hR =>
    obtain ⟨A, n, hA⟩ := hP
    obtain ⟨B, m, hB⟩ := hR
    refine ⟨A * Q^m + B * Q^n, n + m, ?_⟩
    intro v hv
    simp only [map_add, map_mul, map_pow, hA v hv, hB v hv, pow_add]
    simpa only [mul_comm] using div_add_div (aeval v A) (aeval v B)
      (pow_ne_zero n hv) (pow_ne_zero m hv)
  | mul_X P i hP =>
    obtain ⟨A, n, hA⟩ := hP
    cases i with
    | none =>
      refine ⟨A, n + 1, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_none, hA v hv, pow_succ]
      rw [div_mul_eq_div_mul_one_div, one_div]
    | some i =>
      refine ⟨A * X i, n, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_some, hA v hv]
      exact div_mul_eq_mul_div _ _ _

def equations (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span (rename (Option.some : σ → Option σ) '' (I : Set (MvPolynomial σ K)) ∪
    {X none * rename (Option.some : σ → Option σ) Q - 1})

def ideal (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) := (equations I Q).radical

theorem ideal_isRadical (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    (ideal I Q).IsRadical := Ideal.radical_isRadical _

theorem mem_locus (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : Option σ → K) :
    v ∈ zeroLocus K (ideal I Q) ↔
      (fun t => v (some t)) ∈ zeroLocus K I ∧
        v none * aeval (fun t => v (some t)) Q = 1 := by
  constructor
  · intro hv
    constructor
    · intro P hP
      have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_left _ ⟨P, hP, rfl⟩)))
      simpa only [aeval_rename, Function.comp_def] using h
    · have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_right _ (Set.mem_singleton _))))
      simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
        map_one, sub_eq_zero] using h
  · rintro ⟨hI, hQ⟩
    have hker : equations I Q ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro P (⟨F, hF, rfl⟩ | rfl)
      · change aeval v (rename some F) = 0
        simpa only [aeval_rename, Function.comp_def] using hI F hF
      · change aeval v (X none * rename some Q - 1) = 0
        simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
          map_one, sub_eq_zero] using hQ
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations I Q) hP v
      (fun F hF => hker hF)

def domain (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Set (zeroLocus K I) := {x | aeval x.val Q ≠ 0}

def graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : zeroLocus K (ideal I Q) :=
  ⟨fun t => t.elim ((aeval x.val.val Q)⁻¹) x.val.val,
    (mem_locus I Q _).mpr ⟨x.val.property, inv_mul_cancel₀ x.property⟩⟩

theorem denominator_ne_zero (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : aeval (fun t => v.val (some t)) Q ≠ 0 := by
  intro h
  have hh := ((mem_locus I Q v.val).mp v.property).2
  rw [h, mul_zero] at hh
  exact zero_ne_one hh

def project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : domain I Q :=
  ⟨⟨fun t => v.val (some t), ((mem_locus I Q v.val).mp v.property).1⟩,
    denominator_ne_zero I Q v⟩

theorem project_graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : project I Q (graph I Q x) = x := rfl

theorem graph_project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : graph I Q (project I Q v) = v := by
  apply Subtype.ext
  funext t
  cases t with
  | some t => rfl
  | none =>
    change (aeval (fun t => v.val (some t)) Q)⁻¹ = v.val none
    symm
    rw [← one_div]
    exact (eq_div_iff (denominator_ne_zero I Q v)).mpr
      ((mem_locus I Q v.val).mp v.property).2

def equiv (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    domain I Q ≃ zeroLocus K (ideal I Q) where
  toFun := graph I Q
  invFun := project I Q
  left_inv := project_graph I Q
  right_inv := graph_project I Q

theorem domain_isOpen (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    letI := AffineClosedPoints.locusTopology I
    IsOpen (domain I Q) := by
  letI := AffineClosedPoints.locusTopology I
  exact (AffineClosedPoints.nonzero_sets_basis I).isOpen (Set.mem_range_self Q)

theorem graph_continuous (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I Q)
    Continuous (graph I Q) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I Q)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal I Q)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  obtain ⟨A, n, hA⟩ := inverse_substitution_fraction Q P
  have hset : graph I Q ⁻¹' {v | aeval v.val P ≠ 0} =
      Subtype.val ⁻¹' {x : zeroLocus K I | aeval x.val A ≠ 0} := by
    ext x
    change aeval (graph I Q x).val P ≠ 0 ↔ aeval x.val.val A ≠ 0
    rw [show aeval (graph I Q x).val P = aeval x.val.val A / (aeval x.val.val Q)^n from
      hA x.val.val x.property]
    simp only [ne_eq, div_eq_zero_iff, pow_ne_zero _ x.property, or_false]
  rw [hset]
  exact ((AffineClosedPoints.nonzero_sets_basis I).isOpen (Set.mem_range_self A)).preimage
    continuous_subtype_val

theorem project_continuous (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I Q)
    Continuous (project I Q) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I Q)
  apply Continuous.subtype_mk
  apply (AffineClosedPoints.nonzero_sets_basis I).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  have hset : (fun v : zeroLocus K (ideal I Q) => (project I Q v).val) ⁻¹'
      {x | aeval x.val P ≠ 0} =
      {v | aeval v.val (rename some P) ≠ 0} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, aeval_rename, Function.comp_def, project]
  change IsOpen ((fun v : zeroLocus K (ideal I Q) => (project I Q v).val) ⁻¹'
    {x | aeval x.val P ≠ 0})
  rw [hset]
  exact (AffineClosedPoints.nonzero_sets_basis (ideal I Q)).isOpen
    (Set.mem_range_self (rename some P))

def homeomorph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal I Q)
    domain I Q ≃ₜ zeroLocus K (ideal I Q) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal I Q)
  exact { equiv I Q with
    continuous_toFun := graph_continuous I Q
    continuous_invFun := project_continuous I Q }

end PhilipponMultiplicity.AffinePrincipalGraph

end
end

section
-- Included implementation: Solutions.PhilipponAffineReindex
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity.AffineReindex
variable {K : Type*} [Field K] {σ τ : Type*}
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K))

def ideal : Ideal (MvPolynomial τ K) := Ideal.comap (rename e.symm).toRingHom I

theorem ideal_isRadical (hI : I.IsRadical) : (ideal e I).IsRadical :=
  hI.comap _

theorem mem_locus (v : τ → K) :
    v ∈ zeroLocus K (ideal e I) ↔ (v ∘ e) ∈ zeroLocus K I := by
  constructor
  · intro hv P hP
    have hmem : rename e P ∈ ideal e I := by
      change rename e.symm (rename e P) ∈ I
      simpa only [rename_rename, e.symm_comp_self, rename_id, AlgHom.id_apply] using hP
    simpa only [aeval_rename] using hv _ hmem
  · intro hv P hP
    have h := hv (rename e.symm P) hP
    simpa only [aeval_rename, Function.comp_assoc, e.self_comp_symm, Function.comp_id] using h

def forward (v : zeroLocus K I) : zeroLocus K (ideal e I) :=
  ⟨v.val ∘ e.symm, (mem_locus e I _).mpr (by
    simpa only [Function.comp_assoc, e.symm_comp_self, Function.comp_id] using v.property)⟩

def backward (v : zeroLocus K (ideal e I)) : zeroLocus K I :=
  ⟨v.val ∘ e, (mem_locus e I _).mp v.property⟩

def equiv : zeroLocus K I ≃ zeroLocus K (ideal e I) where
  toFun := forward e I
  invFun := backward e I
  left_inv v := by
    apply Subtype.ext
    funext t
    simp only [backward, forward, Function.comp_apply, Equiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext
    funext t
    simp only [backward, forward, Function.comp_apply, Equiv.apply_symm_apply]

theorem forward_continuous :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal e I)
    Continuous (forward e I) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal e I)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal e I)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  have h := (AffineClosedPoints.nonzero_sets_basis I).isOpen (Set.mem_range_self (rename e.symm P))
  simpa only [Set.preimage_ofPred_eq, forward, aeval_rename] using h

theorem backward_continuous :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal e I)
    Continuous (backward e I) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal e I)
  apply (AffineClosedPoints.nonzero_sets_basis I).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  have h := (AffineClosedPoints.nonzero_sets_basis (ideal e I)).isOpen (Set.mem_range_self (rename e P))
  simpa only [Set.preimage_ofPred_eq, backward, aeval_rename] using h

def homeomorph :
    letI := AffineClosedPoints.locusTopology I
    letI := AffineClosedPoints.locusTopology (ideal e I)
    zeroLocus K I ≃ₜ zeroLocus K (ideal e I) := by
  letI := AffineClosedPoints.locusTopology I
  letI := AffineClosedPoints.locusTopology (ideal e I)
  exact { equiv e I with
    continuous_toFun := forward_continuous e I
    continuous_invFun := backward_continuous e I }

end PhilipponMultiplicity.AffineReindex

end
end

section
-- Included implementation: Solutions.PhilipponAffineNeighborhoods
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity
universe u v w

theorem affine_neighborhoods_construction
    (K : Type u) [Field K] [IsAlgClosed K]
    (σ : Type v) [Finite σ] (I : Ideal (MvPolynomial σ K))
    (X : Type w) [TopologicalSpace X] :
    letI : TopologicalSpace (MvPolynomial.zeroLocus K I) :=
      TopologicalSpace.induced
        (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
        inferInstance
    ∀ (d : X → MvPolynomial.zeroLocus K I), Topology.IsEmbedding d →
      IsLocallyClosed (Set.range d) →
      ∀ (x : X) (W : Set X), IsOpen W → x ∈ W →
        ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
          ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
          ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
              (TopologicalSpace.induced
                (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
                inferInstance),
            (∃ L : σ → MvPolynomial (Fin n) K,
              ∀ z : S, ∀ t, (d z.val).val t = MvPolynomial.aeval (a z).val (L t)) ∧
            (∀ i : Fin n, ∃ P Q : MvPolynomial σ K,
              ∀ z : S, MvPolynomial.aeval (d z.val).val Q ≠ 0 ∧
                (a z).val i = MvPolynomial.aeval (d z.val).val P /
                  MvPolynomial.aeval (d z.val).val Q) := by
  classical
  letI : TopologicalSpace (zeroLocus K I) := AffineClosedPoints.locusTopology I
  intro d hd hX x W hW hxW
  obtain ⟨O, C, hO, hC, hOC⟩ := hX
  obtain ⟨E, hE, hEW⟩ := hd.isInducing.isOpen_iff.mp hW
  have hxOC : d x ∈ O ∩ C := by rw [← hOC]; exact Set.mem_range_self x
  have hxE : d x ∈ E := by
    change x ∈ d ⁻¹' E
    rw [hEW]
    exact hxW
  obtain ⟨_, ⟨Q, rfl⟩, hxQ, hQOE⟩ :=
    (AffineClosedPoints.nonzero_sets_basis I).exists_subset_of_mem_open
      (show d x ∈ O ∩ E from ⟨hxOC.1, hxE⟩) (hO.inter hE)
  let S : Set X := {z | aeval (d z).val Q ≠ 0}
  have hS : IsOpen S :=
    ((AffineClosedPoints.nonzero_sets_basis I).isOpen (Set.mem_range_self Q)).preimage hd.continuous
  have hSW : S ⊆ W := by
    intro z hz
    rw [← hEW]
    exact (hQOE hz).2
  have hSC (z : S) : d z.val ∈ C := by
    have hz : d z.val ∈ O ∩ C := by rw [← hOC]; exact Set.mem_range_self z.val
    exact hz.2
  let G := AffineClosedSubsets.ideal I C
  letI : TopologicalSpace (zeroLocus K G) := AffineClosedPoints.locusTopology G
  let c : C ≃ₜ zeroLocus K G := AffineClosedSubsets.homeomorph I C hC
  let T := AffinePrincipalGraph.domain G Q
  let f : S → T := fun z => ⟨c ⟨d z.val, hSC z⟩, z.property⟩
  let j : T → zeroLocus K I := fun y => (c.symm y.val).val
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.comp
    (c.symm.isEmbedding.comp IsEmbedding.subtypeVal)
  have hf : IsEmbedding f := by
    apply hj.of_comp_iff.mp
    have hcomp : j ∘ f = d ∘ Subtype.val := by
      funext z
      change (c.symm (c ⟨d z.val, hSC z⟩)).val = d z.val
      rw [c.symm_apply_apply]
    rw [hcomp]
    exact hd.comp IsEmbedding.subtypeVal
  have hf_surj : Function.Surjective f := by
    intro y
    have hyQ : aeval (j y).val Q ≠ 0 := y.property
    have hyOC : j y ∈ O ∩ C := ⟨(hQOE hyQ).1, (c.symm y.val).property⟩
    rw [← hOC] at hyOC
    obtain ⟨z, hz⟩ := hyOC
    have hzS : z ∈ S := by
      change aeval (d z).val Q ≠ 0
      rw [hz]
      exact hyQ
    refine ⟨⟨z, hzS⟩, ?_⟩
    apply hj.injective
    change (c.symm (c ⟨d z, hSC ⟨z, hzS⟩⟩)).val = j y
    rw [c.symm_apply_apply]
    exact hz
  let cS : S ≃ₜ T := hf.toHomeomorphOfSurjective hf_surj
  let H := AffinePrincipalGraph.ideal G Q
  letI : TopologicalSpace (zeroLocus K H) := AffineClosedPoints.locusTopology H
  let b : S ≃ₜ zeroLocus K H := cS.trans (AffinePrincipalGraph.homeomorph G Q)
  letI : Fintype σ := Fintype.ofFinite σ
  let n := Fintype.card (Option σ)
  let r : Option σ ≃ Fin n := Fintype.equivFin (Option σ)
  let J := AffineReindex.ideal r H
  letI : TopologicalSpace (zeroLocus K J) := AffineClosedPoints.locusTopology J
  let a : S ≃ₜ zeroLocus K J := b.trans (AffineReindex.homeomorph r H)
  have haval (z : S) (t : Fin n) :
      (a z).val t = (r.symm t).elim ((aeval (d z.val).val Q)⁻¹) (d z.val).val := rfl
  refine ⟨S, hS, hxQ, hSW, n, J,
    AffineReindex.ideal_isRadical r H (AffinePrincipalGraph.ideal_isRadical G Q),
    a, ?_, ?_⟩
  · refine ⟨fun t => MvPolynomial.X (r (some t)), ?_⟩
    intro z t
    rw [aeval_X, haval, r.symm_apply_apply]
    rfl
  · intro t
    cases ht : r.symm t with
    | none =>
      refine ⟨1, Q, fun z => ⟨z.property, ?_⟩⟩
      rw [haval, ht, Option.elim_none, map_one, one_div]
    | some s =>
      refine ⟨MvPolynomial.X s, 1, fun z => ⟨by simp, ?_⟩⟩
      rw [haval, ht, Option.elim_some, map_one, div_one, aeval_X]

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity
universe u v w

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (σ : Type v) [Finite σ] (I : Ideal (MvPolynomial σ K))
    (X : Type w) [TopologicalSpace X] :
    letI : TopologicalSpace (MvPolynomial.zeroLocus K I) :=
      TopologicalSpace.induced
        (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
        inferInstance
    ∀ (d : X → MvPolynomial.zeroLocus K I), Topology.IsEmbedding d →
      IsLocallyClosed (Set.range d) →
      ∀ (x : X) (W : Set X), IsOpen W → x ∈ W →
        ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
          ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
          ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
              (TopologicalSpace.induced
                (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
                inferInstance),
            (∃ L : σ → MvPolynomial (Fin n) K,
              ∀ z : S, ∀ t, (d z.val).val t = MvPolynomial.aeval (a z).val (L t)) ∧
            (∀ i : Fin n, ∃ P Q : MvPolynomial σ K,
              ∀ z : S, MvPolynomial.aeval (d z.val).val Q ≠ 0 ∧
                (a z).val i = MvPolynomial.aeval (d z.val).val P /
                  MvPolynomial.aeval (d z.val).val Q) := by
  exact affine_neighborhoods_construction K σ I X
