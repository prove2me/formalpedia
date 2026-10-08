-- Prove2me | solution 1 for Rado.rado_defect_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:29:54.773787+00:00
-- url     : https://prove2.me/submissions/c70cc91b-0e9f-4124-a248-ef4d3b921b5a

import Mathlib

set_option autoImplicit false

namespace Rado

open Module Submodule

/-- Weak duality for Rado's theorem. If `J` carries a linearly independent partial transversal
`v` of the family `A`, then `|J| ≤ |ι \ S| + dim span (⋃_{i ∈ S} A i)` for every `S ⊆ ι`. -/
lemma pk_defect_le {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite)
    (J : Finset ι) (v : ι → V) (hv : ∀ j ∈ J, v j ∈ A j) (hind : LinearIndepOn k v (J : Set ι))
    (S : Finset ι) :
    J.card ≤ Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by
  have hfin : (⋃ i ∈ S, A i).Finite := Set.Finite.biUnion S.finite_toSet (fun i _ => hA i)
  have : FiniteDimensional k (span k (⋃ i ∈ S, A i)) := FiniteDimensional.span_of_finite k hfin
  have hli : LinearIndepOn k v ((J ∩ S : Finset ι) : Set ι) :=
    hind.mono (by intro j hj; exact (Finset.mem_inter.1 hj).1)
  have h1 : (J ∩ S).card ≤ finrank k (span k (⋃ i ∈ S, A i)) := by
    have h2 : finrank k (span k (v '' ((J ∩ S : Finset ι) : Set ι))) = (J ∩ S).card := by
      have := finrank_span_eq_card hli
      rw [← Set.image_eq_range] at this
      simpa only [Finset.coe_sort_coe, Fintype.card_coe] using this
    rw [← h2]
    refine Submodule.finrank_mono (span_mono ?_)
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨hjJ, hjS⟩ := Finset.mem_inter.1 hj
    exact Set.mem_iUnion₂.2 ⟨j, hjS, hv j hjJ⟩
  have h3 : (J \ S).card ≤ Sᶜ.card := by
    refine Finset.card_le_card ?_
    intro j hj
    exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2
  have h4 := Finset.card_sdiff_add_card_inter J S
  omega

end Rado

open Rado

theorem solution {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite)
    (J : Finset ι) (v : ι → V) (hv : ∀ j ∈ J, v j ∈ A j) (hind : LinearIndepOn k v (J : Set ι))
    (S : Finset ι) :
    J.card ≤ Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) :=
  pk_defect_le A hA J v hv hind S

#print axioms solution
