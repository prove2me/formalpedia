-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:52:07.89052+00:00
-- url     : https://prove2.me/submissions/21db2247-f002-46ee-9948-737de568ca97

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
section
noncomputable section
namespace QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
private theorem subtype_transport {A B : Type u} {Label : Type*} (e : A=B)
    (f : A → Label) (g : B → Label) (hfg : ∀ a,f a=g (cast e a)) (u : Label) :
    {a : A // f a=u}={b : B // g b=u} := by
  cases e
  have hf : f=g := funext hfg
  cases hf
  rfl
private theorem owner_rx_apply (S : OddScale) (n : ℕ) (h : (n+2)%2=1)
    (c : OwnerCarrier S (n+2)) :
    owner S (n+2) c = rxSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
        if_pos h) c) := by
  change @Eq (Vertex (state S (n+1)).presentation)
    (if h' : (n+2)%2=1 then
      rxSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
          if_pos h') c)
     else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h') c)))
    (rxSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
        if_pos h) c))
  exact dif_pos h
end QEC.Coding.BDL26ConnectedSyndromeMass
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (n : ℕ) (h : (n+2)%2=1)
    (u : Vertex (state S (n+1)).presentation) :
    OwnerFiber S (n+2) u = RXFiber (state S (n+1)).presentation S u :=
  subtype_transport
    (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from if_pos h)
    (owner S (n+2)) (rxSyndromeOwner (state S (n+1)).presentation S)
    (owner_rx_apply S n h) u
end QEC.Coding.BDL26ConnectedSyndromeMass
